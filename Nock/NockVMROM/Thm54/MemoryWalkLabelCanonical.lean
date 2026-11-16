/-
  Nock/NockVMROM/Thm54/MemoryWalkLabelCanonical.lean

The honest side of the twenty-first move.  The memory walk certificate
  (`MemoryChipAssignment.oneForestWalk`, `Trans.WalkGatesSat`) is stated over the walk columns
  `curCol` / `chldCol` / `foCol` of the family's BFS row list at `R.memoryNodeVal`.  Under the
  `MemoryWalkLabelObligations` — the node value is `RLC^γ` of the paper's `x^mem` label vector
, and each row's fanout / child cells are the state's and the declared
  `lc`/`rc` (`:1428`, `:2031`) — those columns are exactly what the in-gate expressions of
  `MemoryWalkLabel` evaluate to on the canonical gathered row: the base selectors are one-hot at
  the row's state, roles `0..14` carry the three cells, the two hosts `45`/`46` carry the children's
  state tags, slot `7` is `γ` and slot `3` is `α`.  So each in-gate gate is the mask times the
  corresponding `WalkGatesSat` equation.

  Paper: the paper.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm
import Nock.WalkInGate

namespace Nock.NockVMROM.Thm54
namespace MemoryWalkLabelCanonical

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.MemoryTable
open Module
open scoped Polynomial
open CoordinateBasis
open CoordinateCompiler
open MixedCoordinateCompiler
open MonolithicRAP
open StrictExtension
open OptimizedMemoryCoreInventory
open OptimizedMemoryCodec
open OptimizedMemorySemanticRealization
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemorySameExecution
open OptimizedMemoryCanonicalSatisfaction
open MemoryWalkLabel

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-! ## The honest walk columns at the `x^mem` label -/

section WalkColumns

theorem memoryWalkRows_getElem?_row (i : Fin R.problem.cfg.memRows) :
    ∃ t, R.memoryWalkRows[(i : ℕ)]? = some t ∧ t.label = R.problem.exec.memoryRowAt i := by
  have hlen : R.memoryWalkRows.length = R.problem.cfg.memRows := by
    have := R.problem.exec.memoryRows_length
    simpa [ExactExecution.memoryRows, PlusIOSegmentedFamily.memoryWalkRows,
      List.length_map] using this
  have hi : (i : ℕ) < R.memoryWalkRows.length := by rw [hlen]; exact i.isLt
  refine ⟨R.memoryWalkRows[(i : ℕ)], List.getElem?_eq_getElem hi, ?_⟩
  show _ = R.problem.exec.memoryRows.get (Fin.cast R.problem.exec.memoryRows_length.symm i)
  simp [ExactExecution.memoryRows, PlusIOSegmentedFamily.memoryWalkRows, List.getElem_map]
  rfl

/-- `cur(i+1)` is `RLC^γ` of the row's `x^mem` label vector. -/
theorem curCol_eq_rlc_label
    (hEnc : ∀ t, R.memoryNodeVal t = Walk.rlc R.walkGamma (memoryLabelVec t.label.2.2))
    (i : Fin R.problem.cfg.memRows) :
    Walk.curCol R.memoryNodeVal R.memoryWalkRows ((i : ℕ) + 1) =
      Walk.rlc R.walkGamma (memoryLabelVec (R.problem.exec.memoryPubAt i)) := by
  obtain ⟨t, ht, hl⟩ := memoryWalkRows_getElem?_row (R := R) i
  simp only [Walk.curCol, Nat.add_sub_cancel, ht, Option.map_some, Option.getD_some, hEnc, hl]
  rfl

theorem foCol_eq_fanout
    (htopo : ∀ t ∈ R.memoryWalkRows,
      t.label.1 = t.label.2.2.st ∧
        fanoutMem t.label.1 = t.children.length ∧
        childLinkMem t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.memRows) :
    Walk.foCol R.memoryWalkRows ((i : ℕ) + 1) = fanoutMem (R.problem.exec.memoryPubAt i).st := by
  obtain ⟨t, ht, hl⟩ := memoryWalkRows_getElem?_row (R := R) i
  obtain ⟨hst, hfan, -⟩ := htopo t (List.mem_of_getElem? ht)
  simp only [Walk.foCol, Nat.add_sub_cancel, ht, Option.map_some, Option.getD_some]
  rw [← hfan, hst, hl]
  rfl

/-- `chld(i+1, l)` is `RLC^γ` of the declared payload of slot `l−1`: the hosted child tag and
the parent's `lc`/`rc` cell, which by `childLinkMem` is the child's own
`x^mem` label vector. -/
theorem chldCol_eq_childVec
    (hEnc : ∀ t, R.memoryNodeVal t = Walk.rlc R.walkGamma (memoryLabelVec t.label.2.2))
    (htopo : ∀ t ∈ R.memoryWalkRows,
      t.label.1 = t.label.2.2.st ∧
        fanoutMem t.label.1 = t.children.length ∧
        childLinkMem t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.memRows) (l : ℕ) (hl1 : 1 ≤ l)
    (hl : l ≤ fanoutMem (R.problem.exec.memoryPubAt i).st) :
    Walk.chldCol R.memoryNodeVal R.memoryWalkRows ((i : ℕ) + 1) l =
      Walk.rlc R.walkGamma
        (childVecN (R.problem.exec.memoryPubAt i)
          (fun j => memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) j) (l - 1)) := by
  obtain ⟨t, ht, hlbl⟩ := memoryWalkRows_getElem?_row (R := R) i
  obtain ⟨hst, hfan, hlink⟩ := htopo t (List.mem_of_getElem? ht)
  have hpub : R.problem.exec.memoryPubAt i = t.label.2.2 := by
    show (R.problem.exec.memoryRowAt i).2.2 = _
    rw [hlbl]
  have hfo : fanoutMem (R.problem.exec.memoryPubAt i).st = t.children.length := by
    rw [hpub, ← hst, hfan]
  have hlt : l - 1 < t.children.length := by omega
  have hle2 : l - 1 < 2 := by
    have := fanoutMem_le_two (R.problem.exec.memoryPubAt i).st
    omega
  obtain ⟨c, hc⟩ : ∃ c, t.children[l - 1]? = some c :=
    ⟨t.children[l - 1], List.getElem?_eq_getElem hlt⟩
  have hcell : c.label.2.2.pt = memCell t.label ⟨l - 1, hle2⟩ := by
    have hlinkj := hlink ⟨l - 1, hle2⟩ (by
      show l - 1 < fanoutMem t.label.1
      rw [hst, ← hpub]; omega)
    simp only [Walk.NTree.childLabel, Walk.NTree.childOpt, hc, Option.map_some] at hlinkj
    exact Option.some.inj hlinkj
  have htag : memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) (l - 1) =
      mstateTagField c.label.2.2.st := by
    simp [memChildStateTagCol, ht, hc]
  simp only [Walk.chldCol, Nat.add_sub_cancel, ht, Option.bind_some, hc, Option.map_some,
    Option.getD_some, hEnc]
  congr 1
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, (j : ℕ) = l - 1 := ⟨⟨l - 1, hle2⟩, rfl⟩
  rw [← hj, childVecN_fin]
  have hj' : (⟨l - 1, hle2⟩ : Fin 2) = j := Fin.ext hj.symm
  rw [hj'] at hcell
  rw [← hj] at htag
  symm
  apply childVec_eq_labelVec
  · exact htag
  · rw [hpub, childCell_eq_memCell, hcell]

theorem walkCC_eq_childSum
    (hEnc : ∀ t, R.memoryNodeVal t = Walk.rlc R.walkGamma (memoryLabelVec t.label.2.2))
    (htopo : ∀ t ∈ R.memoryWalkRows,
      t.label.1 = t.label.2.2.st ∧
        fanoutMem t.label.1 = t.children.length ∧
        childLinkMem t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.memRows) :
    Trans.walkCC (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha ((i : ℕ) + 1) =
      ∑ l ∈ Finset.Icc 1 (fanoutMem (R.problem.exec.memoryPubAt i).st),
        R.memoryWalkAlpha ^ l *
          Walk.rlc R.walkGamma
            (childVecN (R.problem.exec.memoryPubAt i)
              (fun j => memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) j) (l - 1)) := by
  rw [Trans.walkCC, foCol_eq_fanout htopo i]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  rw [chldCol_eq_childVec hEnc htopo i l hl.1 hl.2]

end WalkColumns

/-! ## Canonical row values -/

section Canonical

variable (A : SampledIOSameExecutionAssignment R p)
  (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {h : ℕ} (orbit : StrictOrbitDomain F 3 h)

include hnodes

/-- Base selectors of the canonical row are one-hot at the row's state. -/
theorem canonical_selector_cur (i : Fin R.problem.cfg.memRows) (st : MState) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace (mopCol st) =
      if st = (R.problem.exec.memoryPubAt i).st then 1 else 0 := by
  have hj : mopCol st < 6 := by cases st <;> simp [mopCol]
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i ⟨mopCol st, hj⟩
  rw [this]
  simp only [encodedRowAt, encode, encodeBase, semanticRowAt, stateSelector, stateIndex]
  generalize (R.problem.exec.memoryPubAt i).st = s
  cases st <;> cases s <;> simp [mopCol]

theorem canonical_selector_next (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (st : MState) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).traceNext (mopCol st) =
      if st = (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).st then 1 else 0 := by
  have hj : mopCol st < 6 := by cases st <;> simp [mopCol]
  have := canonical_base_next A nodes hnodes b chalVal pubVal orbit i hi hsucc ⟨mopCol st, hj⟩
  rw [this]
  simp only [encodedRowAt, encode, encodeBase, semanticRowAt, stateSelector, stateIndex]
  generalize (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).st = s
  cases st <;> cases s <;> simp [mopCol]

/-- Extension role `r < 15` of the canonical row is table column `4 + r` of the exact row. -/
theorem canonical_cellRole_cur (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) (r : ℕ) (hr : r < 15) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace r =
      (exactMemoryRowEnv A i).trace (4 + r) := by
  have := canonical_table_role A nodes hnodes b chalVal pubVal orbit pins i (4 + r)
    (by omega) (by omega) (by omega)
  rwa [show 4 + r - 4 = r by omega] at this

theorem canonical_cellRole_next (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (r : ℕ) (hr : r < 15) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext r =
      (exactMemoryRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace (4 + r) := by
  let role : MemoryTablePayloadRole := .inl ⟨r, hr⟩
  have hrow := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
    i hi hsucc (extensionEquiv (.inl role))
    (OptimizedMemoryCanonicalSatisfaction.payload_extIndex_ne_rootMask role)
  rw [extensionEquiv.symm_apply_apply] at hrow
  have hidx : ((extensionEquiv (.inl role) : Fin 56) : ℕ) = r := by
    simp [extensionEquiv_apply, extensionIndex, role]
  have hcol : (memoryTableSourceColumn role : ℕ) = 4 + r := by
    simp [memoryTableSourceColumn, role]
  have hnot : (memoryTableSourceColumn role : ℕ) ≠ 31 ∧
      (memoryTableSourceColumn role : ℕ) ≠ 32 := by
    rw [hcol]; omega
  simp only [encodedRowAt, encode, encodeExtension] at hrow
  rw [semanticRowAt_table_eq_exact A _ role hnot] at hrow
  rw [hcol, hidx] at hrow
  exact hrow

/-- Host role `45`/`46` of the canonical row carries the declared child state tag. -/
theorem canonical_host_cur (i : Fin R.problem.cfg.memRows) (j : Fin 2) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (childTagHostRole j) =
      memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) j := by
  fin_cases j
  · have := canonical_gather_sampled_index A nodes hnodes b chalVal pubVal orbit i (8 : Fin 14)
      (by decide)
    simpa [childTagHostRole, sampledMemoryRoleValue] using this
  · have := canonical_gather_sampled_index A nodes hnodes b chalVal pubVal orbit i (9 : Fin 14)
      (by decide)
    simpa [childTagHostRole, sampledMemoryRoleValue] using this

theorem canonical_host_next (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (j : Fin 2) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext (childTagHostRole j) =
      memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1 + 1) j := by
  fin_cases j
  · have hrow := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
      i hi hsucc (extensionEquiv (.inr (.inr (.inl (8 : Fin 14)))))
      (by decide)
    rw [extensionEquiv.symm_apply_apply] at hrow
    simpa [encodedRowAt, encode, encodeExtension, semanticRowAt, sampledMemoryRoleValue,
      extensionEquiv_apply, extensionIndex, childTagHostRole] using hrow
  · have hrow := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
      i hi hsucc (extensionEquiv (.inr (.inr (.inl (9 : Fin 14)))))
      (by decide)
    rw [extensionEquiv.symm_apply_apply] at hrow
    simpa [encodedRowAt, encode, encodeExtension, semanticRowAt, sampledMemoryRoleValue,
      extensionEquiv_apply, extensionIndex, childTagHostRole] using hrow

/-- Walk roles `31`/`32`/`33` of the canonical row are `ln`/`count`/`acc` at walk node `i+1`. -/
theorem canonical_walkRole_cur (i : Fin R.problem.cfg.memRows) (r : Fin 6) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (31 + (r : ℕ)) =
      (exactMemoryWalkRowEnv A i).trace r := by
  have := canonical_gather_walk_current A nodes hnodes b chalVal pubVal orbit i r
  simpa [extensionEquiv_apply, extensionIndex] using this

theorem canonical_walkRole_next (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (r : Fin 6) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext (31 + (r : ℕ)) =
      (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace r := by
  have := canonical_gather_walk_next A nodes hnodes b chalVal pubVal orbit i hi hsucc r
  simpa [extensionEquiv_apply, extensionIndex] using this

omit hnodes in
theorem canonical_chal_alpha (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).chal 3 = R.memoryWalkAlpha := by
  change (∑ k : Fin 3, chalVal ((memorySourceTemplate b).col0 3 .challenge 3 + (k : ℕ)) • b k)
    = R.memoryWalkAlpha
  exact pins.walkChallenge

omit hnodes in
theorem canonical_chal_gamma (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).chal 7 = R.walkGamma := by
  change (∑ k : Fin 3, chalVal ((memorySourceTemplate b).col0 3 .challenge 7 + (k : ℕ)) • b k)
    = R.walkGamma
  exact pins.walkGamma

omit hnodes in
theorem canonical_pub_initialCount (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).pub 0 =
      R.memoryWalkAlpha ^ R.problem.cfg.kMem := by
  change (∑ k : Fin 3, pubVal ((memorySourceTemplate b).col0 3 .publicVal 0 + (k : ℕ)) • b k)
    = R.memoryWalkAlpha ^ R.problem.cfg.kMem
  exact pins.walkInitialCount

omit hnodes in
/-- Seed public unread: gathered `pub 1` is the `pkgPub` reconstruction,
    not a pin (`walkSeed` deleted). -/
theorem canonical_pub_seed_unpinned (pubVal : ℕ → F)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).pub 1 =
      ∑ k : Fin 3, pubVal ((memorySourceTemplate b).col0 3 .publicVal 1 + (k : ℕ)) • b k :=
  rfl

theorem canonical_firstMask (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 4 = firstMask i := by
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (4 : Fin 6)
  simpa [encodedRowAt, encode, encodeBase, semanticRowAt] using this

theorem canonical_lastMask (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 5 = lastMask i := by
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  simpa [encodedRowAt, encode, encodeBase, semanticRowAt] using this

/-! ### Cell coordinates of the exact row -/

omit hnodes in
theorem exactRow_cellCoord (i : Fin R.problem.cfg.memRows) (k : Fin 5) :
    (exactMemoryRowEnv A i).trace (4 + (k : ℕ)) =
      cellCoord (R.problem.exec.memoryPubAt i).pt k := by
  fin_cases k <;> rfl

omit hnodes in
theorem exactRow_childCellCoord (i : Fin R.problem.cfg.memRows) (j : Fin 2) (k : Fin 5) :
    (exactMemoryRowEnv A i).trace (4 + (cellBase j + (k : ℕ))) =
      cellCoord (childCell (R.problem.exec.memoryPubAt i) j) k := by
  fin_cases j <;> fin_cases k <;> rfl

/-! ## The in-gate walk gates on canonical rows -/

/-- The value hypotheses of the `curReader` lemmas at canonical row `i`. -/
theorem canonical_cur_values (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (∀ st, ((curReader (F := F)).sel st).eval
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      if st = (R.problem.exec.memoryPubAt i).st then 1 else 0) ∧
    (∀ k : Fin 5, ((curReader (F := F)).col k).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      cellCoord (R.problem.exec.memoryPubAt i).pt k) ∧
    (∀ (j : Fin 2) (k : Fin 5), ((curReader (F := F)).col (cellBase j + (k : ℕ))).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      cellCoord (childCell (R.problem.exec.memoryPubAt i) j) k) ∧
    (∀ j, (childTagHost (curReader (F := F)) j).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) j) := by
  refine ⟨fun st => canonical_selector_cur A nodes hnodes b chalVal pubVal orbit i st, ?_, ?_, ?_⟩
  · intro k
    rw [curReader_col_eval, canonical_cellRole_cur A nodes hnodes b chalVal pubVal orbit pins i k
      (by have := k.isLt; omega)]
    exact exactRow_cellCoord A i k
  · intro j k
    rw [curReader_col_eval, canonical_cellRole_cur A nodes hnodes b chalVal pubVal orbit pins i
      (cellBase j + (k : ℕ)) (by fin_cases j <;> (have := k.isLt; simp [cellBase]; omega))]
    exact exactRow_childCellCoord A i j k
  · intro j
    exact canonical_host_cur A nodes hnodes b chalVal pubVal orbit i j

/-- The value hypotheses of the `nextReader` lemmas at canonical row `i` (successor row
`i + 1`). -/
theorem canonical_next_values (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows) :
    (∀ st, ((nextReader (F := F)).sel st).eval
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      if st = (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).st then 1 else 0) ∧
    (∀ k : Fin 5, ((nextReader (F := F)).col k).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      cellCoord (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).pt k) ∧
    (∀ (j : Fin 2) (k : Fin 5), ((nextReader (F := F)).col (cellBase j + (k : ℕ))).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      cellCoord (childCell (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩) j) k) ∧
    (∀ j, (childTagHost (nextReader (F := F)) j).eval
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1 + 1) j) := by
  have hsucc := halign i hi
  refine ⟨fun st => canonical_selector_next A nodes hnodes b chalVal pubVal orbit i hi hsucc st,
    ?_, ?_, ?_⟩
  · intro k
    rw [nextReader_col_eval, canonical_cellRole_next A nodes hnodes b chalVal pubVal orbit i hi
      hsucc k (by have := k.isLt; omega)]
    exact exactRow_cellCoord A _ k
  · intro j k
    rw [nextReader_col_eval, canonical_cellRole_next A nodes hnodes b chalVal pubVal orbit i hi
      hsucc (cellBase j + (k : ℕ)) (by fin_cases j <;> (have := k.isLt; simp [cellBase]; omega))]
    exact exactRow_childCellCoord A _ j k
  · intro j
    exact canonical_host_next A nodes hnodes b chalVal pubVal orbit i hi hsucc j

omit hnodes in
theorem canonical_walkGates_facts (P : MemoryChipAssignment A) :
    Trans.WalkGatesSat
      (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows)
      A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem) R.problem.cfg.memRows := by
  have hw := (exact_forest_walk_sources P).1
  exact hw

/-- **The in-gate accumulation step holds on every canonical row**. -/
theorem canonical_walkAccStepInGate (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal) (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    (walkAccStepInGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i with henvK
  set envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i with henvF
  obtain ⟨hEnc, htopo⟩ := P.obligations.2.2.2
  rw [walkAccStepInGate_eval, canonical_lastMask A nodes hnodes b chalVal pubVal orbit i]
  have hdm :=
    OptimizedMemoryCanonicalSatisfaction.canonical_physical_dequeueMask
      A nodes hnodes b chalVal pubVal orbit i
  by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
  · obtain ⟨hselN, hcolN, hchildN, htagN⟩ :=
      canonical_next_values A nodes hnodes b chalVal pubVal orbit halign i hi
    have hγ : (walkGammaChallenge (F := F)).eval envK envF = R.walkGamma :=
      canonical_chal_gamma A nodes b chalVal pubVal orbit pins i
    have hα : (walkAlphaChallenge (F := F)).eval envK envF = R.memoryWalkAlpha :=
      canonical_chal_alpha A nodes b chalVal pubVal orbit pins i
    set i1 : Fin R.problem.cfg.memRows := ⟨(i : ℕ) + 1, hi⟩ with hi1
    have hL := labelRLC_eval (nextReader (F := F)) envK envF (R.problem.exec.memoryPubAt i1)
      R.walkGamma hselN hcolN hγ
    have hCC := childSumCC_eval (nextReader (F := F)) envK envF (R.problem.exec.memoryPubAt i1)
      R.memoryWalkAlpha R.walkGamma
      (fun j => memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1 + 1) j) hselN hchildN hα hγ htagN
    have hsucc := halign i hi
    have hlnN := canonical_walkRole_next A nodes hnodes b chalVal pubVal orbit i hi hsucc (0 : Fin 6)
    have haccN := canonical_walkRole_next A nodes hnodes b chalVal pubVal orbit i hi hsucc (2 : Fin 6)
    have hacc := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (2 : Fin 6)
    have hcnt := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (1 : Fin 6)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at hlnN haccN hacc hcnt
    simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked] at hlnN haccN hacc hcnt
    have hstep := ((exact_forest_walk_sources_masked P).2.2.2.2 ((i : ℕ) + 1)
      (by omega) (by omega)).2.2
    rw [Trans.reified_walk_acc_stepMasked_sound] at hstep
    have hcur := curCol_eq_rlc_label hEnc i1
    have hcc := walkCC_eq_childSum hEnc htopo i1
    have hcw := Trans.c_mul_walkCC (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha (A.exact.memoryWalk.count ((i : ℕ) + 1))
      ((i : ℕ) + 1 + 1)
    simp only [hi1, Fin.val_mk] at hcur hcc
    have hdeqVal : algebraMap F K (envF.trace MemoryWalkLabel.dequeueMaskCol) =
        1 - Walk.rootMask (K := K) R.problem.cfg.kMem ((i : ℕ) + 1 + 1) := by
      rw [henvF, hdm]
      simp [Walk.rootMask, MemoryWalkLabel.dequeueMaskCol]
      split_ifs <;> simp <;> omega
    rw [lnRole, accRole, countRole, MemoryWalkLabel.dequeueMaskCol, hlnN, haccN, hacc, hcnt, hL, hCC,
      ← hcur, ← hcc, hdeqVal]
    have hzero : (1 - Walk.rootMask (K := K) R.problem.cfg.kMem ((i : ℕ) + 1 + 1)) *
        A.exact.memoryWalk.ln ((i : ℕ) + 1 + 1) *
        Walk.curCol R.memoryNodeVal R.memoryWalkRows ((i : ℕ) + 1 + 1) +
          (memoryAccInGate A ((i : ℕ) + 1 + 1) - memoryAccInGate A ((i : ℕ) + 1) -
        A.exact.memoryWalk.count ((i : ℕ) + 1) *
          Trans.walkCC (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
            (Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha ((i : ℕ) + 1 + 1)) = 0 := by
      rw [hcw]
      linear_combination hstep
    have hlast0 : lastMask (F := F) i = 0 := by
      simp [lastMask, show (i : ℕ) + 1 ≠ R.problem.cfg.memRows by omega]
    rw [hlast0, sub_zero, map_one, one_mul]
    convert hzero using 1
    ring
  · have hlast : lastMask (F := F) i = 1 := by
      simp [lastMask, show (i : ℕ) + 1 = R.problem.cfg.memRows by omega]
    have hdm0 : envF.trace MemoryWalkLabel.dequeueMaskCol = 0 := by
      rw [henvF, hdm]
      simp [MemoryWalkLabel.dequeueMaskCol,
        show (i : ℕ) + 1 = R.problem.cfg.memRows by omega]
    rw [hlast, hdm0]
    simp

/-- **The in-gate count step holds on every canonical row**. -/
theorem canonical_walkCountStepInGate (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal) (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    (walkCountStepInGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i with henvK
  set envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i with henvF
  obtain ⟨hEnc, htopo⟩ := P.obligations.2.2.2
  rw [walkCountStepInGate_eval, canonical_lastMask A nodes hnodes b chalVal pubVal orbit i]
  by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
  · obtain ⟨hselN, -, -, -⟩ :=
      canonical_next_values A nodes hnodes b chalVal pubVal orbit halign i hi
    have hα : (walkAlphaChallenge (F := F)).eval envK envF = R.memoryWalkAlpha :=
      canonical_chal_alpha A nodes b chalVal pubVal orbit pins i
    set i1 : Fin R.problem.cfg.memRows := ⟨(i : ℕ) + 1, hi⟩ with hi1
    have hCM := selectorCM_eval (nextReader (F := F)) envK envF (R.problem.exec.memoryPubAt i1)
      R.memoryWalkAlpha hselN hα
    have hsucc := halign i hi
    have hcntN := canonical_walkRole_next A nodes hnodes b chalVal pubVal orbit i hi hsucc (1 : Fin 6)
    have hcnt := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (1 : Fin 6)
    simp only [Fin.val_one] at hcntN hcnt
    simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked] at hcntN hcnt
    have hstep := ((canonical_walkGates_facts A P).2.2.2.2 ((i : ℕ) + 1) (by omega) (by omega)).2.1
    rw [Trans.reified_walk_count_step_sound] at hstep
    have hfo := foCol_eq_fanout htopo i1
    simp only [hi1, Fin.val_mk] at hfo
    rw [countRole, hcntN, hcnt, hCM, ← hfo, hstep, sub_self, mul_zero]
  · have hlast : lastMask (F := F) i = 1 := by
      simp [lastMask, show (i : ℕ) + 1 = R.problem.cfg.memRows by omega]
    rw [hlast]
    simp

/-- **The in-gate initial count holds on every canonical row**. -/
theorem canonical_walkCount1InGate (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (walkCount1InGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i with henvK
  set envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i with henvF
  obtain ⟨hEnc, htopo⟩ := P.obligations.2.2.2
  rw [walkCount1InGate_eval, canonical_firstMask A nodes hnodes b chalVal pubVal orbit i]
  by_cases hi0 : (i : ℕ) = 0
  · have hfirst : firstMask (F := F) i = 1 := by simp [firstMask, hi0]
    obtain ⟨hsel, -, -, -⟩ := canonical_cur_values A nodes hnodes b chalVal pubVal orbit pins i
    have hα : (walkAlphaChallenge (F := F)).eval envK envF = R.memoryWalkAlpha :=
      canonical_chal_alpha A nodes b chalVal pubVal orbit pins i
    have hCM := selectorCM_eval (curReader (F := F)) envK envF (R.problem.exec.memoryPubAt i)
      R.memoryWalkAlpha hsel hα
    have hcnt := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (1 : Fin 6)
    simp only [Fin.val_one] at hcnt
    simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked] at hcnt
    have hic := canonical_pub_initialCount A nodes b chalVal pubVal orbit pins i
    have h1 := (canonical_walkGates_facts A P).2.2.1
    rw [Trans.reified_walk_count1_sound] at h1
    have hfo := foCol_eq_fanout htopo i
    rw [hfirst, countRole, hcnt, hCM, hic, ← hfo]
    simp only [hi0, Nat.zero_add]
    rw [h1, sub_self, mul_zero]
  · have hfirst : firstMask (F := F) i = 0 := by simp [firstMask, hi0]
    rw [hfirst]
    simp

/-- **The in-gate initial accumulator holds on every canonical row**: first row is a root, so `acc(1) = α^k · cc(1)`. -/
theorem canonical_walkAccInitInGate (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (walkAccInitInGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i with henvK
  set envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i with henvF
  obtain ⟨hEnc, htopo⟩ := P.obligations.2.2.2
  rw [walkAccInitInGate_eval, canonical_firstMask A nodes hnodes b chalVal pubVal orbit i]
  by_cases hi0 : (i : ℕ) = 0
  · have hfirst : firstMask (F := F) i = 1 := by simp [firstMask, hi0]
    obtain ⟨hsel, hcol, hchild, htag⟩ :=
      canonical_cur_values A nodes hnodes b chalVal pubVal orbit pins i
    have hγ : (walkGammaChallenge (F := F)).eval envK envF = R.walkGamma :=
      canonical_chal_gamma A nodes b chalVal pubVal orbit pins i
    have hα : (walkAlphaChallenge (F := F)).eval envK envF = R.memoryWalkAlpha :=
      canonical_chal_alpha A nodes b chalVal pubVal orbit pins i
    have hL := labelRLC_eval (curReader (F := F)) envK envF (R.problem.exec.memoryPubAt i)
      R.walkGamma hsel hcol hγ
    have hCC := childSumCC_eval (curReader (F := F)) envK envF (R.problem.exec.memoryPubAt i)
      R.memoryWalkAlpha R.walkGamma
      (fun j => memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) j) hsel hchild hα hγ htag
    have hln := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (0 : Fin 6)
    have hacc := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (2 : Fin 6)
    simp only [Fin.val_zero, Fin.val_two, Nat.add_zero] at hln hacc
    simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked] at hln hacc
    have hic := canonical_pub_initialCount A nodes b chalVal pubVal orbit pins i
    have h1 := (exact_forest_walk_sources_masked P).2.2.2.1
    rw [Trans.reified_walk_accInitMasked_sound] at h1
    have hcc := walkCC_eq_childSum hEnc htopo i
    have hcw := Trans.c_mul_walkCC (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha (R.memoryWalkAlpha ^ R.problem.cfg.kMem) 1
    rw [hfirst, accRole, hacc, hCC, hic, ← hcc]
    simp only [hi0, Nat.zero_add] at hcc ⊢
    have hzero : memoryAccInGate A 1 -
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem *
          Trans.walkCC (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
            (Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha 1) = 0 := by
      rw [hcw]
      linear_combination h1
    rw [hzero, mul_zero]
  · have hfirst : firstMask (F := F) i = 0 := by simp [firstMask, hi0]
    rw [hfirst]
    simp

/-- Canonical row exposes the dedicated queue-inverse at role `55`. -/
theorem canonical_walkInv (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace walkInvRole =
      walkInvValue A i := by
  have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inr (.inr (.inr (.inr (0 : Fin 1))))))
    (by decide)
  have hidx : ((extensionEquiv (.inr (.inr (.inr (.inr (0 : Fin 1))))) : Fin 56) : ℕ) =
      walkInvRole := by
    simp [extensionEquiv_apply, extensionIndex, walkInvRole]
  rw [hidx, Equiv.symm_apply_apply] at hrow
  simpa [encodedRowAt, encode, encodeExtension, semanticRowAt] using hrow

omit hnodes in
theorem exact_memory_walkSat (P : MemoryChipAssignment A) :
    Walk.WalkSat
      (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows)
      A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem) R.problem.cfg.memRows :=
  (Trans.walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).1
    (canonical_walkGates_facts A P)

omit hnodes in
theorem exact_memory_walkRows_length :
    R.memoryWalkRows.length = R.problem.cfg.memRows := by
  have := R.problem.exec.memoryRows_length
  simpa [ExactExecution.memoryRows, PlusIOSegmentedFamily.memoryWalkRows,
    List.length_map] using this

omit hnodes in
theorem exact_memory_bfsValid :
    Walk.BFSValidF R.problem.cfg.kMem (Walk.foCol R.memoryWalkRows)
      R.problem.cfg.memRows := by
  have this := Walk.foCol_BFSValidF R.problem.exec.memoryForest
    R.problem.exec.memoryForest_nonempty
  change Walk.BFSValidF R.problem.exec.memoryForest.length
      (Walk.foCol (Walk.bfsForest R.problem.exec.memoryForest))
      (Walk.bfsForest R.problem.exec.memoryForest).length at this
  rw [← show R.memoryWalkRows = Walk.bfsForest R.problem.exec.memoryForest from rfl] at this
  rwa [exact_memory_walkRows_length, R.problem.exec.memory_root_count] at this

omit hnodes in
theorem exact_memory_tiling :
    R.problem.cfg.kMem + Walk.Sf (Walk.foCol R.memoryWalkRows) R.problem.cfg.memRows =
      R.problem.cfg.memRows := by
  have this := Walk.foCol_Sf_tilingF R.problem.exec.memoryForest
    R.problem.exec.memoryForest_nonempty
  change R.problem.exec.memoryForest.length +
      Walk.Sf (Walk.foCol (Walk.bfsForest R.problem.exec.memoryForest))
        (Walk.bfsForest R.problem.exec.memoryForest).length =
    (Walk.bfsForest R.problem.exec.memoryForest).length at this
  rw [← show R.memoryWalkRows = Walk.bfsForest R.problem.exec.memoryForest from rfl] at this
  rwa [exact_memory_walkRows_length, R.problem.exec.memory_root_count] at this

omit hnodes in
/-- WalkSat + BFS tiling: last-row `count = ln` with no order hypothesis
(`kMem + Sf = h` so the powers agree). -/
theorem exact_memory_last_count_eq_ln (P : MemoryChipAssignment A) :
    A.exact.memoryWalk.count R.problem.cfg.memRows =
      A.exact.memoryWalk.ln R.problem.cfg.memRows := by
  have hsat := exact_memory_walkSat A P
  have hn : 0 < R.problem.cfg.memRows := R.problem.cfg.memRows_pos
  have hln := Walk.ln_closed hsat R.problem.cfg.memRows (by omega) le_rfl
  have hcnt := Walk.count_closed hsat R.problem.cfg.memRows (by omega) le_rfl
  rw [hcnt, hln, ← pow_add, exact_memory_tiling]

omit hnodes in
/-- Non-last walk indices have `count ≠ ln` under `h ≤ orderOf α`. -/
theorem exact_memory_nonlast_count_ne_ln (P : MemoryChipAssignment A)
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < R.problem.cfg.memRows) :
    A.exact.memoryWalk.count i ≠ A.exact.memoryWalk.ln i := by
  have hsat := exact_memory_walkSat A P
  have hord' : R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha :=
    hord (by omega)
  have hneq := (Nock.RedTeam.Batch478.honest_ratio_gate (K := K)
      exact_memory_bfsValid exact_memory_tiling hord').1 i hi1 hih
  have hln := Walk.ln_closed hsat i hi1 (Nat.le_of_lt hih)
  have hcnt := Walk.count_closed hsat i hi1 (Nat.le_of_lt hih)
  rw [hcnt, hln]
  convert hneq using 1
  rw [pow_add]


theorem canonical_queueWitnessGates (P : MemoryChipAssignment A)
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ MemoryWalkLabel.queueWitnessGates (F := F),
      g.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro g hg
  simp only [MemoryWalkLabel.queueWitnessGates, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  have hlast := canonical_lastMask A nodes hnodes b chalVal pubVal orbit i
  have hln := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (0 : Fin 6)
  have hcnt := canonical_walkRole_cur A nodes hnodes b chalVal pubVal orbit i (1 : Fin 6)
  have hinv := canonical_walkInv A nodes hnodes b chalVal pubVal orbit i
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at hln hcnt
  simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked] at hln hcnt
  rcases hg with rfl | rfl
  · rw [walkQueueNonEmpty_eval, hlast]
    by_cases hlastRow : (i : ℕ) + 1 = R.problem.cfg.memRows
    · have : lastMask (F := F) i = 1 := by simp [lastMask, hlastRow]
      rw [this, sub_self, map_zero, zero_mul]
    · have : lastMask (F := F) i = 0 := by simp [lastMask, hlastRow]
      rw [this, sub_zero, map_one, one_mul]
      simp [walkInvRole, lnRole, countRole] at hinv hln hcnt ⊢
      rw [hinv, hln, hcnt]
      have hne : A.exact.memoryWalk.count ((i : ℕ) + 1) ≠
          A.exact.memoryWalk.ln ((i : ℕ) + 1) :=
        exact_memory_nonlast_count_ne_ln A P hord (by omega) (by omega)
      simp [walkInvValue, hne, inv_mul_cancel₀ (sub_ne_zero.mpr hne)]
  · rw [walkQueueTiling_eval, hlast]
    by_cases hlastRow : (i : ℕ) + 1 = R.problem.cfg.memRows
    · have : lastMask (F := F) i = 1 := by simp [lastMask, hlastRow]
      have heq := exact_memory_last_count_eq_ln A P
      rw [this, map_one, one_mul]
      simp [lnRole, countRole] at hln hcnt ⊢
      rw [hln, hcnt, hlastRow, heq, sub_self]
    · have : lastMask (F := F) i = 0 := by simp [lastMask, hlastRow]
      rw [this, map_zero, zero_mul]

/-- **Every in-gate walk gate vanishes on every canonical memory row.** -/
theorem canonical_inGateWalkGates (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal) (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ MemoryWalkLabel.inGateWalkGates (F := F),
      g.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro g hg
  simp only [MemoryWalkLabel.inGateWalkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact canonical_walkCount1InGate A nodes hnodes b chalVal pubVal orbit P pins i
  · exact canonical_walkAccInitInGate A nodes hnodes b chalVal pubVal orbit P pins i
  · exact canonical_walkCountStepInGate A nodes hnodes b chalVal pubVal orbit P pins halign i
  · exact canonical_walkAccStepInGate A nodes hnodes b chalVal pubVal orbit P pins halign i

end Canonical

end
end MemoryWalkLabelCanonical
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical.canonical_inGateWalkGates
