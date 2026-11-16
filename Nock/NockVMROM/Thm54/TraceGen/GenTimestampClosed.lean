/-
  Nock/NockVMROM/Thm54/TraceGen/GenTimestampClosed.lean

  **`timestampClosed` is free wherever the memory rows are a *specialization*.**

  `TimestampClosedAt α ts := ∃ e : ℕ, ts = α ^ e` (`AxisSoundness.lean:42`, and its verbatim twin
  `GenericHonestData.MemoryTimestampClosedAt`, `:673`) is orbit membership of a memory-record
  timestamp.

  This module measures how much of that premise survives once the rows are known to be a
  specialization of an α-free template, and the answer is: on the memory side, all of it, with no
  acceptance, no seed condition and no counted event.

  ## §A.  The memory side is unscaled, so the closed form is definitional

  `MemoryRowTemplate.specialize` (`SemanticTimestampStrategy.lean:435`) sets

      mem := specializeMemRec α (decide (memoryMemRecKind stamp.state =.active))
               stamp.recordExponent pub.mem

  and `specializeMemRec` (`:349`) is `if active then { record with ts := α ^ exponent } else
  MemRec.zero`.  So an *active* specialized memory row has `ts = α ^ stamp.recordExponent` by
  construction of the function, and a *padding* row is the exact zero record — whose `ts = 0`,
  which for `α ≠ 0` is **not** in the orbit.  That is why `timestampClosed` is guarded by
  `memoryMemRecKind … =.active` rather than being stated for all rows.

  **The compute/memory asymmetry is real.**  The memory side takes the **unscaled** `specializeMemRec` at every occurrence
  (`SemanticTimestampStrategy.lean:443`, the only memory-row producer in that file), so nothing on
  this route depends on the declined pin.

  ## §B.  Consequently it is free at three scopes, and each has a different reading

  1. **`∀ T : ProductionStrategy F K`** — `productionStrategy_timestampClosed`.  Every production
     execution *is* a template specialization: `specializedProblem`
     (`TemplateRawJointSoundness.lean:36-40`) defines
     `exec := (T.afterSeed ⟨z, hz⟩).executionTemplate.specialize alphaM`, and `specializedExec`
     (`ProductionP8Containment.lean:104`) is that field.  No hypothesis, no acceptance.
  2. **`∀ E : BuildableNockExecution F K` that holds a commitment** — `timestampClosed_of_data`.
     `Data.memoryOK` (`HonestCommitment.lean:685`) asks `MemoryNodesOK` at every committed root,
     whose fourth conjunct is `MemoryTimestampSpecializesAt` (`:450`), and `Data.memory_rows`
     (`:683`) identifies the committed forest's row projection with `E.exec.memoryForest`.  So a
     commitment carries the closed form.  ⚠️ **This is a discharge only when the commitment has an
     independent supplier.**  On the reconstruction route it is circular: `memoryAssemblyOf`
     (`GenericHonestData.lean:1377-1381`) sets `memoryOK := memoryNodesOf_ok E M` (`:1290`), whose
     `M : MemoryRecordPremises E` *is* the structure carrying `timestampClosed`, and `dataOfRecord`
     (`:1934`) forwards that field.  The independent suppliers are the generated ones — `genData_memoryOK`
     and `genComputeSkeleton_memForest_OK_air` (`GenGenericMemory.lean:91`) — which prove
     `MemoryNodesOK` from request well-formedness alone.
  3. **`∀ program the generator accepts`** — `genProgram_timestampClosed`, at the AIR-ordered
     generated memory forest, with `hOK` discharged by `genComputeSkeleton_memForest_OK_air`.
     Scope caveat: this is the *unthreaded* `genMemForestFromTree` forest.  Live configurations
     commit `threadGenForest … (genMemForestFromTree …)` (`GenTierAMemAccept.lean:1026,1029`); for those
     use route 2, since every live configuration holds a `Data`.

  ## §C.  What this does *not* close, and where the chain actually stops

  Free membership therefore
  removes the *recovery* obstruction — but it does not deliver the served half, and the reason is
  recorded in `Iff` form here rather than asserted:

  * `timestampClosed_does_not_pin_the_exponent` — membership gives *an* exponent and no more:
    `α ^ e = α ^ (e + orderOf α)`, so identifying *which* record a verify exponent names needs an
    orbit window (`ExactServedMemoryTrace.timestampPowersNodup`, `ServedMemoryTrace.lean:610`),
    which is a separate carried field and not a consequence of closure.
  * `slotSemantics_needs_a_noun_step` — even a recovered record is a tuple of *fingerprints*.
    `ServedLookupBridge.SkeletonSlotSemantics` (`:72`) is a `Noun.slot` equation on the committed
    **skeleton**'s nouns, and the only route to it, `slotSemantics_of_served` (`:220`), wants
    membership in `servedTuplesOf T`.  `E` already carries served lookups —
    `SemanticTrace.ServedNounLookup` (`:46`) has a `served : GlobalCarryAxis.ServedLookup` field and
    sits inside `RowStateNeeds` (`:174`), a field of C5 — so what is missing is not the *lookup*
    but the **identification** of the lookup's `(root, axis, child)` nouns with the skeleton's
    `(subject, skeletonMemoryAxis s 1, evaluation)`.  That is a fingerprint→noun step, and
    `recordPair_not_in_skeletonComparisons` says the record root/child pairs are
    not entries of `P8Census.skeletonComparisons`, so `combined_pairFaithful` supplies nothing
    there.  `GenericHonestData.lean:46-50` states the same residual in the author's own words.

  Nothing here is asserted as a negative: §C's two declarations are the *reductions*, not verdicts.

  ## Not claimed

  No `∀ E, Data E`.  No carrier field is added, `MemoryRecordPremises` keeps its two fields, and
  `ResidualPremises` is untouched.  `Gen.lean` is unedited.
-/
import Nock.NockVMROM.Thm54.PairedRecordIOResult
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.TraceGen.GenGenericMemory
import Nock.NockVMROM.Thm54.TraceGen.GenExactExecution
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## §A.  Reading the specialization equation

`MemoryTimestampSpecializesAt` (`SemanticTimestampStrategy.lean:544`) is the paper's memory-row
timestamp sentence.  These two projections are the whole of §A; everything below is transport. -/

/-- **An active specialized memory row's timestamp is a power of `α`.**  The witness is the
committed `ℕ` exponent, read straight off the specialization equation. -/
theorem closed_of_specializes {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row)
    (hact : memoryMemRecKind row.1 = .active) :
    GenericHonestData.MemoryTimestampClosedAt α row.2.2.mem.ts := by
  obtain ⟨hst, -, hts, -⟩ := h
  have hact' : memoryMemRecKind stamp.state = .active := by rw [← hst]; exact hact
  exact ⟨stamp.recordExponent, by rw [hts, if_pos hact']⟩

/-- The exponent is the committed one, not merely some exponent. -/
theorem ts_eq_pow_of_specializes {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row)
    (hact : memoryMemRecKind row.1 = .active) :
    row.2.2.mem.ts = α ^ stamp.recordExponent := by
  obtain ⟨hst, -, hts, -⟩ := h
  have hact' : memoryMemRecKind stamp.state = .active := by rw [← hst]; exact hact
  rw [hts, if_pos hact']

/-- **Padding rows, stated rather than glossed.**  A padding memory row is the exact production
zero record. -/
theorem memRec_zero_of_specializes {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row)
    (hpad : memoryMemRecKind row.1 = .padding) :
    row.2.2.mem = ComputeTable.MemRec.zero := by
  obtain ⟨hst, -, -, hz⟩ := h
  exact hz (by rw [← hst]; exact hpad)

/-- …so a padding row's timestamp is `0`. -/
theorem ts_eq_zero_of_specializes {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row)
    (hpad : memoryMemRecKind row.1 = .padding) :
    row.2.2.mem.ts = 0 := by
  rw [memRec_zero_of_specializes h hpad]
  rfl

/-- **…and `0` is not in the orbit**, so the `.active` guard on `timestampClosed` is not decoration:
the premise is false at padding rows and the guard is what makes it true. -/
theorem not_closed_zero {α : K} (hα : α ≠ 0) :
    ¬ GenericHonestData.MemoryTimestampClosedAt α (0 : K) := by
  rintro ⟨e, he⟩
  exact pow_ne_zero e hα he.symm

/-! ## §A′.  One template row, one specialized template execution -/

/-- Every active row a memory template specializes to has a closed timestamp. -/
theorem memoryRowTemplate_timestampClosed (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (hact : memoryMemRecKind (T.specialize α lmb).1 = .active) :
    GenericHonestData.MemoryTimestampClosedAt α (T.specialize α lmb).2.2.mem.ts :=
  closed_of_specializes (T.specializes α lmb) hact

theorem memoryRowTemplate_ts_eq_pow (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (hact : memoryMemRecKind (T.specialize α lmb).1 = .active) :
    (T.specialize α lmb).2.2.mem.ts = α ^ T.timestamp.recordExponent :=
  ts_eq_pow_of_specializes (T.specializes α lmb) hact

theorem memoryRowTemplate_padding_zero (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (hpad : memoryMemRecKind (T.specialize α lmb).1 = .padding) :
    (T.specialize α lmb).2.2.mem = ComputeTable.MemRec.zero :=
  memRec_zero_of_specializes (T.specializes α lmb) hpad

/-- **Every memory row of a specialized α-free execution template.**  `∀` template, `∀ α`. -/
theorem templateExec_timestampClosed {Tc : ExactConfigTemplate F K}
    (Etpl : ExactExecutionTemplate Tc) (α lmb : K) :
    ∀ row ∈ (Etpl.specialize α lmb).memoryRows,
      memoryMemRecKind row.1 = .active →
        GenericHonestData.MemoryTimestampClosedAt α row.2.2.mem.ts := by
  intro row hrow hact
  rw [ExactExecutionTemplate.specialize_memoryRows] at hrow
  obtain ⟨T, -, hT⟩ := List.mem_map.mp hrow
  subst hT
  exact memoryRowTemplate_timestampClosed T α lmb hact

theorem templateExec_padding_zero {Tc : ExactConfigTemplate F K}
    (Etpl : ExactExecutionTemplate Tc) (α lmb : K) :
    ∀ row ∈ (Etpl.specialize α lmb).memoryRows,
      memoryMemRecKind row.1 = .padding →
        row.2.2.mem = ComputeTable.MemRec.zero := by
  intro row hrow hpad
  rw [ExactExecutionTemplate.specialize_memoryRows] at hrow
  obtain ⟨T, -, hT⟩ := List.mem_map.mp hrow
  subst hT
  exact memoryRowTemplate_padding_zero T α lmb hpad

/-! ## §B.1.  `∀ T : ProductionStrategy` — no premise, no acceptance, no seed condition -/

section Production

variable [Fintype K] [DecidableEq K]

/-- The raw `(z, alphaM)`-specialized problem's memory rows are closed at `alphaM`. -/
theorem specializedProblem_timestampClosed
    (V : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ∀ row ∈ (TemplateRawJointSoundness.specializedProblem V z hz α lmb).exec.memoryRows,
      memoryMemRecKind row.1 = .active →
        GenericHonestData.MemoryTimestampClosedAt α row.2.2.mem.ts :=
  templateExec_timestampClosed (V.afterSeed ⟨z, hz⟩).executionTemplate α lmb

variable [CharP K (ringChar K)]

/-- **The headline of §1.**  For *any* production strategy, any nonzero seed and any sampled
timestamp challenge, every active memory row of the specialized execution has a timestamp in the
orbit of `α`.  There is no acceptance hypothesis, no seed condition, no counted event, and no
`Data`.

The conclusion is stated at `(T.specializedCfg z hz α lmb).challenges.α`, i.e. exactly the shape
`MemoryRecordPremises.timestampClosed` asks for on this configuration. -/
theorem productionStrategy_timestampClosed
    (T : ProductionP8Containment.ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ∀ i : Fin (T.specializedCfg z hz α lmb).memRows,
      memoryMemRecKind ((T.specializedExec z hz α lmb).memoryRowAt i).1 = .active →
        GenericHonestData.MemoryTimestampClosedAt
          (T.specializedCfg z hz α lmb).challenges.α
          ((T.specializedExec z hz α lmb).memoryRowAt i).2.2.mem.ts := by
  intro i hact
  exact specializedProblem_timestampClosed T.verifier.raw.timestamp z hz α lmb _
    (ExactExecution.memoryRowAt_mem (T.specializedExec z hz α lmb) i) hact

/-- The padding half at production scope. -/
theorem productionStrategy_padding_zero
    (T : ProductionP8Containment.ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ∀ i : Fin (T.specializedCfg z hz α lmb).memRows,
      memoryMemRecKind ((T.specializedExec z hz α lmb).memoryRowAt i).1 = .padding →
        ((T.specializedExec z hz α lmb).memoryRowAt i).2.2.mem = ComputeTable.MemRec.zero := by
  intro i hpad
  exact templateExec_padding_zero
    (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate α lmb _
    (ExactExecution.memoryRowAt_mem (T.specializedExec z hz α lmb) i) hpad

end Production

/-! ## §B.1′.  The node-level form, which is what the axis tree reads

`AxisSoundness.TimestampNodeClosedAt` is `TimestampClosedAt` restricted to the two states that
consume a memory record, and `timestampNodeClosedAt_spec` turns it into `AxisBridge.TsNode`.  Both
are free on a specialized forest. -/

section Node

variable [Fintype K] [DecidableEq K]

/-- Node-level closure from the row-level specialization equation. -/
theorem timestampNodeClosed_of_specializes {α : K} {stamp : MemoryTimestampRow}
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTimestampSpecializesAt α stamp (NTree.label t)) :
    TimestampNodeClosedAt α t := by
  unfold TimestampNodeClosedAt
  cases hs : (NTree.label t).1 with
  | decompose => exact trivial
  | halt => exact trivial
  | read_root =>
      have ha : memoryMemRecKind (NTree.label t).1 = FPSlotKind.active := by
        rw [hs]; rfl
      exact closed_of_specializes h ha
  | verify_child =>
      have ha : memoryMemRecKind (NTree.label t).1 = FPSlotKind.active := by
        rw [hs]; rfl
      exact closed_of_specializes h ha

/-- **Every node of a specialized memory forest is timestamp-closed.**  `∀` template, `∀ α`. -/
theorem templateForest_timestampNodeClosed {Tc : ExactConfigTemplate F K}
    (Etpl : ExactExecutionTemplate Tc) (α lmb : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (ht : t ∈ bfsForest (Etpl.specialize α lmb).memoryForest) :
    TimestampNodeClosedAt α t := by
  have hforest :
      (Etpl.specialize α lmb).memoryForest =
        Etpl.memoryForest.map (mapNTree (fun row : MemoryRowTemplate (K := K) =>
          row.specialize α lmb)) := rfl
  rw [hforest, bfsForest_mapNTree] at ht
  obtain ⟨u, -, hu⟩ := List.mem_map.mp ht
  subst hu
  refine timestampNodeClosed_of_specializes
    (stamp := (NTree.label u).timestamp) ?_
  rw [mapNTree_label]
  exact MemoryRowTemplate.specializes _ α _

/-- …and therefore satisfies `AxisBridge.TsNode` at the canonical exponent map, which is what
`exactAxisTree` labels its nodes with. -/
theorem templateForest_tsNode {Tc : ExactConfigTemplate F K}
    (Etpl : ExactExecutionTemplate Tc) (α lmb : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (ht : t ∈ bfsForest (Etpl.specialize α lmb).memoryForest) :
    Nock.AxisBridge.TsNode (timestampExpAt α) { z := α, β := 0, γ := 0 } t :=
  timestampNodeClosedAt_spec α t (templateForest_timestampNodeClosed Etpl α lmb t ht)

end Node

/-! ## §B.2.  `∀ E` that holds a commitment

`Data.memoryOK` is `MemoryNodesOK` at every committed root, whose fourth conjunct is the same
specialization equation; `Data.memory_rows` identifies the committed row projection with the
supplied forest.  So a commitment already contains the closed form.

⚠️ Circularity warning, stated because it decides whether this is a *discharge*: on the
reconstruction route `dataOfRecord` proves `memoryOK` **from** `M.timestampClosed`, so using this
there is circular.  It is a discharge exactly when `Data` has an independent supplier — the
generated route does (`genComputeSkeleton_memForest_OK_air`, §B.3). -/

/-- Every active memory row of a committed execution is timestamp-closed. -/
theorem memoryRows_closed_of_data {E : BuildableNockExecution F K} (D : Data E) :
    ∀ row ∈ E.exec.memoryRows,
      memoryMemRecKind row.1 = .active →
        GenericHonestData.MemoryTimestampClosedAt E.cfg.challenges.α row.2.2.mem.ts := by
  intro row hrow hact
  rw [E.exec_encode, ExactExecution.encodeMem_memoryRows] at hrow
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  rw [ExactExecution.memoryRows, ← D.memory_rows, bfsForest_mapNTree] at hr0
  obtain ⟨u, hu, hlbl⟩ := List.mem_map.mp hr0
  obtain ⟨u0, hu0, hmap⟩ := List.mem_map.mp hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu0
  have hrow' : r0 = (NTree.label u0).row := by
    rw [← hlbl, ← hmap, mapNTree_label]
  have hOK := D.memoryOK c hc u0 hin
  rw [encodeRow_pub_mem_ts, hrow']
  exact closed_of_specializes hOK.2.2.2 (by rw [← hrow']; simpa using hact)

/-- The same at `MemoryRecordPremises.timestampClosed`'s indexed shape. -/
theorem timestampClosed_of_data {E : BuildableNockExecution F K} (D : Data E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        GenericHonestData.MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  fun i hact =>
    memoryRows_closed_of_data D _ (ExactExecution.memoryRowAt_mem E.exec i) hact

/-- Honest `ver` from a commitment: each committed memory node carries
`BindMemoryRow`, whose last conjunct is the honesty equation on `ver`. -/
theorem honestVer_of_data {E : BuildableNockExecution F K} (D : Data E) :
    ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  intro row hrow
  rw [E.exec_encode, ExactExecution.encodeMem_memoryRows] at hrow
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  rw [ExactExecution.memoryRows, ← D.memory_rows, bfsForest_mapNTree] at hr0
  obtain ⟨u, hu, hlbl⟩ := List.mem_map.mp hr0
  obtain ⟨u0, hu0, hmap⟩ := List.mem_map.mp hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu0
  have hrow' : r0 = (NTree.label u0).row := by
    rw [← hlbl, ← hmap, mapNTree_label]
  have hOK := D.memoryOK c hc u0 hin
  rw [encodeRow_pub_ver, encodeRow_pub_st, hrow', hOK.2.2.1.2.2.1]
  exact hOK.2.2.1.2.2.2.2.2.2

/-- **`MemoryRecordPremises` in full from a commitment.**  `axisNat` was already free on `E`
(`axisNat_of_execution`); with `timestampClosed` and honest `ver` free from `Data`, the whole
three-field structure is.  Same circularity caveat as above. -/
def memoryRecordPremises_of_data {E : BuildableNockExecution F K} (D : Data E) :
    GenericHonestData.MemoryRecordPremises E :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed E
    (timestampClosed_of_data D) (honestVer_of_data D)

/-- The padding half from a commitment. -/
theorem memoryRows_padding_zero_of_data {E : BuildableNockExecution F K} (D : Data E) :
    ∀ row ∈ E.exec.memoryRows,
      memoryMemRecKind row.1 = .padding →
        row.2.2.mem = ComputeTable.MemRec.zero := by
  intro row hrow hpad
  rw [E.exec_encode, ExactExecution.encodeMem_memoryRows] at hrow
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  rw [ExactExecution.memoryRows, ← D.memory_rows, bfsForest_mapNTree] at hr0
  obtain ⟨u, hu, hlbl⟩ := List.mem_map.mp hr0
  obtain ⟨u0, hu0, hmap⟩ := List.mem_map.mp hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu0
  have hrow' : r0 = (NTree.label u0).row := by
    rw [← hlbl, ← hmap, mapNTree_label]
  have hOK := D.memoryOK c hc u0 hin
  have hpad0 : memoryMemRecKind r0.1 = .padding := by simpa using hpad
  rw [encodeRow_pub_mem_of_not_active r0 (by rw [hpad0]; decide), hrow']
  exact memRec_zero_of_specializes hOK.2.2.2 (by rw [← hrow']; exact hpad0)

/-! ## §B.3.  `∀ program the generator accepts` -/

section Generated

variable {K' : Type} [Field K']

/-- `InTree` is preserved by relabelling.  (The reverse direction is `inTree_mapNTree`,
`GenAirOrderChildLink.lean:89`; this is the forward one.) -/
theorem inTree_map {α β : Type} (f : α → β) :
    ∀ {u v : NTree α}, InTree u v → InTree (mapNTree f u) (mapNTree f v)
  | _, _, InTree.here _ => InTree.here _
  | _, _, InTree.sub hs ht =>
      InTree.sub
        (by simpa [mapNTree_children] using List.mem_map.mpr ⟨_, hs, rfl⟩)
        (inTree_map f ht)

/-- **The generated carrier's memory rows, from `MemoryNodesOK` on the generated forest.**
Hypothesis-shaped and generic in the forest: `hOK` is exactly `Data.memoryOK`'s obligation, which
`GenGenericMemory` discharges for every accepted program. -/
theorem genExactExecution_timestampClosed
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (hOK : ∀ u ∈ mf, MemoryNodesOK chal.z chal.α (mapNTree GenMemoryRow.node u)) :
    ∀ row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).memoryRows,
      memoryMemRecKind row.1 = .active →
        GenericHonestData.MemoryTimestampClosedAt chal.α row.2.2.mem.ts := by
  intro row hrow hact
  rw [genExactExecution_memoryRows] at hrow
  obtain ⟨n, hn, hrn⟩ := List.mem_map.mp hrow
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ _).mp hn
  have hOKn := hOK u hu (mapNTree GenMemoryRow.node n) (inTree_map _ hin)
  have hspec : MemoryTimestampSpecializesAt chal.α
      (GenMemoryRow.node (NTree.label n)).stamp
      (GenMemoryRow.node (NTree.label n)).row := by
    have := hOKn.2.2.2
    rwa [mapNTree_label] at this
  rw [← hrn, encodeRow_pub_mem_ts]
  exact closed_of_specializes hspec (by rw [← hrn] at hact; simpa using hact)

/-- **`timestampClosed` at the generated memory forest, for every program the generator accepts.**
`hOK` is discharged by `genComputeSkeleton_memForest_OK_air`; the compute tree `ct` is arbitrary,
because the closed form is a memory-side fact.

Scope: `∀ program accepted by genComputeSkeleton`, at the *unthreaded* AIR-ordered forest.  Live
configurations commit the threaded forest; for those use `timestampClosed_of_data`. -/
theorem genProgram_timestampClosed
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (ct : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemForestFromTree (encC chal.z) chal.z chal.α chal.lam
      (bfsAssign (airReorder t)))).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemForestFromTree (encC chal.z) chal.z chal.α chal.lam
      (bfsAssign (airReorder t)))).length ≤ 2 ^ orbit.h) :
    ∀ row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c ct
        (genMemForestFromTree (encC chal.z) chal.z chal.α chal.lam (bfsAssign (airReorder t)))
        hmempos hcomp hmem).memoryRows,
      memoryMemRecKind row.1 = .active →
        GenericHonestData.MemoryTimestampClosedAt chal.α row.2.2.mem.ts :=
  genExactExecution_timestampClosed chal Ksz orbit horb a b c ct _ hmempos hcomp hmem
    (genComputeSkeleton_memForest_OK_air chal.z chal.α h)

end Generated

/-! ## §C.  The two reductions that stop the 1 → 2 → 3 chain

Both are `Iff`/implication statements about what closure does and does not give. -/

section Residual

variable [Fintype K] [DecidableEq K]

/-- **Leg 2: membership does not pin the exponent.**  `TimestampClosedAt` is satisfied by every
member of the orbit, and the orbit repeats with period `orderOf α`, so a closed timestamp has
infinitely many exponents whenever `α` has finite order.  Identifying *which* record a verify-tree
exponent names therefore needs the orbit window carried by
`ExactServedMemoryTrace.timestampPowersNodup`; it is not a consequence of closure. -/
theorem timestampClosed_does_not_pin_the_exponent {α : K} (e : ℕ) :
    GenericHonestData.MemoryTimestampClosedAt α (α ^ e) ∧
      α ^ e = α ^ (e + orderOf α) := by
  refine ⟨⟨e, rfl⟩, ?_⟩
  rw [pow_add, pow_orderOf_eq_one, mul_one]

/-- **Leg 3, localized: what is missing is a noun identification, not a lookup.**

`E` already carries served lookups: `SemanticTrace.ServedNounLookup` (`SemanticTrace.lean:46`) has a
`served : GlobalCarryAxis.ServedLookup` field and sits inside `RowStateNeeds` (`:174`), which is a
field of `ComputeRowSemanticData` (C5) and hence of `E.semanticData`.  What
`ServedLookupBridge.SkeletonSlotSemantics` additionally needs is that the lookup's `(root, axis,
child)` nouns *are* the committed skeleton's `(subject, skeletonMemoryAxis s 1, evaluation)` — and
this theorem shows that identification is the **only** missing step: granted it, the slot facts
follow with nothing else.

That step is a fingerprint→noun identification, and `recordPair_not_in_skeletonComparisons` records that the record root/child pairs are not entries of
`P8Census.skeletonComparisons`, so `combined_pairFaithful` cannot discharge it. -/
theorem slotSemantics_needs_a_noun_step {z : K}
    (s : SemanticStrategy.ComputeRowSkeleton)
    (l0 l9 : SemanticTrace.ServedNounLookup (K := K) z)
    (h0 : s.state = .s0 →
      l0.root = s.subject ∧
        l0.axis = P8Census.skeletonMemoryAxis s 1 ∧
        l0.child = s.evaluation)
    (h9 : s.state = .s9 →
      l9.root = P8Census.skeletonSubformula s 0 .result ∧
        l9.axis = P8Census.skeletonMemoryAxis s 2 ∧
        l9.child = P8Census.skeletonSubformula s 1 .formula) :
    ServedLookupBridge.SkeletonSlotSemantics s := by
  refine ServedLookupBridge.skeletonSlotSemantics_of_served ?_ ?_
  · intro hst
    obtain ⟨hr, ha, hc⟩ := h0 hst
    rw [← hr, ← ha, ← hc]
    exact l0.served
  · intro hst
    obtain ⟨hr, ha, hc⟩ := h9 hst
    rw [← hr, ← ha, ← hc]
    exact l9.served

/-- **Leg 1/2: closure is exactly the recovery step, in both directions.** -/
theorem recovers_iff_closed (α ts : K) :
    α ^ timestampExp α ts = ts ↔ GenericHonestData.MemoryTimestampClosedAt α ts :=
  GenericHonestData.timestampExp_recovers_ts_iff_closed α ts

end Residual

end Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.closed_of_specializes
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.ts_eq_pow_of_specializes
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.memRec_zero_of_specializes
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.not_closed_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.templateExec_timestampClosed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.productionStrategy_timestampClosed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.productionStrategy_padding_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.templateForest_timestampNodeClosed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.templateForest_tsNode
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.timestampClosed_of_data
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.memoryRecordPremises_of_data
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.genExactExecution_timestampClosed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.genProgram_timestampClosed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.timestampClosed_does_not_pin_the_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.slotSemantics_needs_a_noun_step
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed.recovers_iff_closed

