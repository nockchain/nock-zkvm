import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch121Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.MemoryTable
import Nock.NockVM
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `MemoryRecordPremises.timestampClosed` stays named.
It is live `ts = α^e` on **both** `read_root` and `verify_child`.  Served
`read_root` `Service.timestamp` already supplies that equation on emission
records; that is not the extra.  `verify_child` emits no
`responseRecords`, so `derivedResponseIO` /
`SemanticIOPreimage` do not see that row's `mem.ts`.  The missing
hypothesis is field-equality of each live `mem.ts` with some
`Service.record.ts`.  `forestVerifyTimestamps` is wrapping
`α^{timestampExp}`: junk `0` reconstructs `1`, not `mem.ts`.
`intermediate_matching` / `ipre`/`icur` stay AIR matching.
`ForestExponentOrder` and `axisNat` stay named.  Accounting remains
`11+1+2`.  Wrapping reconstruction is not rounded into a consumed-capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch122

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
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
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.ServedMemoryTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Extra still named: live `ts = α^e` on both `read_root` and `verify_child` -/

/-- Paper closed form is existence, not the uniqueness window. -/
theorem timestampClosed_is_existence (α ts : K) :
    MemoryTimestampClosedAt α ts = ∃ e : ℕ, ts = α ^ e :=
  rfl

/-- Same `Prop` as the axis-tree closed form -/
theorem MemoryTimestampClosedAt_eq_TimestampClosedAt (α ts : K) :
    MemoryTimestampClosedAt α ts = TimestampClosedAt α ts :=
  rfl

/-- Live memory-record rows are exactly `read_root` and `verify_child`.
Independent of the production wrapper -/
theorem memoryMemRecKind_active_iff (s : MemoryTable.MState) :
    memoryMemRecKind s = .active ↔ s = .read_root ∨ s = .verify_child := by
  cases s <;> simp [memoryMemRecKind]

/-- Named extra quantifies over every active row, hence both live kinds. -/
theorem premises_timestampClosed_is_existence
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ e : ℕ, (E.exec.memoryRowAt i).2.2.mem.ts = E.cfg.challenges.α ^ e :=
  fun i hact => (timestampClosed_is_existence _ _).mp (M.timestampClosed i hact)

/-- `verify_child` is an active kind, so it is in the extra's quantifier. -/
theorem extra_applies_to_verify_child
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    MemoryTimestampClosedAt E.cfg.challenges.α
      (E.exec.memoryRowAt i).2.2.mem.ts :=
  M.timestampClosed i (by simp [memoryMemRecKind, h])

/-- Served compute-side `Service.timestamp` is the `read_root` emission half.
Independent of the production wrapper -/
theorem service_timestamp_is_closed
    {E : BuildableNockExecution F K}
    (s : ServedMemoryTrace.Service E.cfg E.execA) :
    MemoryTimestampClosedAt E.cfg.challenges.α s.record.ts :=
  ⟨s.exponent, s.timestamp⟩

/-- `recordPartition` identifies this root's `read_root` emissions with
service records.  Not `verify_child` -/
theorem recordPartition_is_read_root_emissions
    {E : BuildableNockExecution F K} (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
      (E.memoryTrace.roots i).services.map ServedMemoryTrace.Service.record :=
  (E.memoryTrace.roots i).recordPartition

/-- Those `read_root` emissions are closed powers.  Not the named extra. -/
theorem timestampClosed_of_root_response_record
    {E : BuildableNockExecution F K} (i : Fin E.cfg.kMem)
    {r : ComputeTable.MemRec K}
    (hr : r ∈ ServedMemoryTrace.rootResponseRecords E.execA i) :
    MemoryTimestampClosedAt E.cfg.challenges.α r.ts := by
  have hmem :
      r ∈ ((E.memoryTrace.roots i).services.map
        ServedMemoryTrace.Service.record) := by
    simpa [recordPartition_is_read_root_emissions] using hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hmem
  exact service_timestamp_is_closed s

/-- The two named NMR extras remain.  `timestampClosed` is not dropped. -/
theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch121.memoryRecordPremises_eta_still_two M

/-- Inverse-BFS reconstruction consumes the named extra, so it does not
inhabit it -/
theorem memoryNodesOf_takes_premises
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    memoryNodesOf E M = memoryForestOf E M :=
  rfl

/-! ## B. Missing hyp is `verify_child` identification, not `True` -/

/-- `verify_child` with honest `ver = false` emits no external IO response.  Independent unfold. -/
theorem verify_child_emits_no_response (pub : MemoryTable.Pub K)
    (h : pub.st = .verify_child) (hver : pub.ver = false) :
    MemoryTable.responseRecords pub = [] := by
  simp [MemoryTable.responseRecords, hver]

/-- That empty list contains no copy of `pub.mem` -/
theorem verify_child_mem_not_in_own_responseRecords
    (pub : MemoryTable.Pub K) (h : pub.st = .verify_child) (hver : pub.ver = false) :
    pub.mem ∉ MemoryTable.responseRecords pub := by
  simp [verify_child_emits_no_response pub h hver]

/-- Canonical raw responses are `responseRecords` of memory rows.
`verify_child` contributes `[]` -/
theorem rawResponses_from_responseRecords
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawResponses =
      exec.memoryRows.flatMap fun row =>
        MemoryTable.responseRecords row.2.2 :=
  rfl

theorem derivedResponseIO_from_rawResponses
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hC : exec.CprimeCoherent) :
    exec.derivedResponseIO =
      exec.rawResponses.map (fun r => NockVM.encRecC r (exec.cprimeOf r)) :=
  ExactExecution.derivedResponseIO_eq_map_encRecC exec hC

/-- `SemanticIOPreimage` response timestamps encode to `derivedResponseIO`.
They do not see a `verify_child` emission -/
theorem semantic_responses_bridge_derivedResponseIO
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticResponses =
      exec.derivedResponseIO :=
  w.responses_bridge

/-- `Fmem` already forces `pub.st = row.1`, so a `verify_child` extra-row
is a `verify_child` emission-row.  Not an identification of timestamps. -/
theorem fmem_forces_state_agreement
    {lbl : MemoryTable.MState × MemoryTable.DTmem K}
    {xout : Fin 2 → Option (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTable.Fmem (K := K) lbl xout) :
    lbl.2.2.st = lbl.1 :=
  h.1

/-- **Missing hypothesis**, independently reconstructed: field-equality of
each live `mem.ts` with some already-held `Service.record.ts` inhabits the
extra.  This is not `True` -/
theorem timestampClosed_of_identified_service_timestamps
    {E : BuildableNockExecution F K}
    (h :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ s : ServedMemoryTrace.Service E.cfg E.execA,
            (E.exec.memoryRowAt i).2.2.mem.ts = s.record.ts) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  obtain ⟨s, hs⟩ := h i hact
  exact ⟨s.exponent, hs.trans s.timestamp⟩

/-! ## C. Wrapping reconstruction is non-vacuous and in the extra's `Prop` -/

/-- Without an exponent witness, `timestampExp` is junk `0`.
Independent of the production wrapper -/
theorem timestampExp_eq_zero_of_not_closed {α ts : K}
    (h : ¬ TimestampClosedAt α ts) :
    timestampExp α ts = 0 := by
  simp [timestampExp, h]

/-- A reconstructed power of a non-closed timestamp is `α^0 = 1`. -/
theorem reconstructed_power_of_not_closed {α ts : K}
    (h : ¬ TimestampClosedAt α ts) :
    α ^ timestampExp α ts = 1 := by
  rw [timestampExp_eq_zero_of_not_closed h, pow_zero]

/-- `0` is never a power of a nonzero `α`.  Same `Prop` as the extra's
per-row conclusion -/
theorem zero_not_closed_of_ne_zero {α : K} (hα : α ≠ 0) :
    ¬ MemoryTimestampClosedAt α 0 := by
  rintro ⟨e, he⟩
  exact pow_ne_zero e hα he.symm

/-- Reconstructing a non-closed zero timestamp yields `1 ≠ 0`.
This is the extra's conclusion applied to the field element `0`, not a
claim that a live row has `ts = 0` -/
theorem reconstructed_power_ne_zero_timestamp {α : K} (hα : α ≠ 0) :
    α ^ timestampExp α 0 = 1 ∧
      ¬ MemoryTimestampClosedAt α 0 ∧
      (1 : K) ≠ 0 := by
  have hnc : ¬ TimestampClosedAt α 0 := by
    simpa [MemoryTimestampClosedAt_eq_TimestampClosedAt] using
      zero_not_closed_of_ne_zero hα
  exact ⟨reconstructed_power_of_not_closed hnc,
    zero_not_closed_of_ne_zero hα, one_ne_zero⟩

/-- Wrapping `ts = 0` is the extra's per-row `Prop`, so the witness is in
the extra's quantifier-shape -/
theorem wrapping_zero_is_extra_conclusion (α : K) :
    MemoryTimestampClosedAt α 0 = ∃ e : ℕ, (0 : K) = α ^ e :=
  timestampClosed_is_existence α 0

/-- Members of `forestVerifyTimestamps` are reconstructed powers of
axis-tree exponents, by construction.  Not live `mem.ts`. -/
theorem mem_forestVerifyTimestamps_is_reconstructed_power
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {ts : K}
    (hts : ts ∈ forestVerifyTimestamps cfg exec) :
    ∃ i : Fin cfg.kMem, ∃ e ∈ verifyExps (exactAxisTree cfg exec i),
      ts = cfg.challenges.α ^ e := by
  unfold forestVerifyTimestamps at hts
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hts
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
  exact ⟨i, e, he, rfl⟩

/-- `exactAxisTree` reads `timestampExp` of each node's `mem.ts`.
Wrapping junk `0` is that choice -/
theorem timestampExpAt_is_timestampExp (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    timestampExpAt α t = timestampExp α (NTree.label t).2.2.mem.ts :=
  rfl

/-! ## D. Intermediate column / `ipre`/`icur` stay AIR matching -/

/-- Structural `intermediate` matching is `LmIO` of reconstructed
`α^{timestampExp}` lists -/
theorem execution_structural_intermediate_matching
    (E : BuildableNockExecution F K) :
    IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
      (forestVerifyTimestamps E.cfg E.execA) :=
  E.memoryTrace.axisStructural.intermediate_matching

/-- `axisStructural` is the three-field structural refinement.  It omits
`ExactAxisRefinement.timestamp_closed` -/
theorem axisStructural_eta_omits_timestamp_closed
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec) :
    R =
      { ancestry := R.ancestry
        read_timestamps_nodup := R.read_timestamps_nodup
        intermediate_matching := R.intermediate_matching } := by
  cases R
  rfl

/-- `E.memoryTrace.axisStructural` is that structural object, not the
full refinement that would carry `timestamp_closed` -/
theorem execution_axisStructural_is_structural
    (E : BuildableNockExecution F K) :
    ExactAxisStructuralRefinement E.cfg E.execA :=
  E.memoryTrace.axisStructural

/-- Adjacent-row `icur = ipre` is the already-compiled AIR accumulator
hand-off.  It is not an exponent witness for `mem.ts`. -/
theorem memory_chain_is_icur_ipre_handoff
    (E : BuildableNockExecution F K) :
    ∀ i : Fin E.cfg.memRows, ∀ hi : (i : ℕ) + 1 < E.cfg.memRows,
      (E.exec.memoryPubAt i).icur =
        (E.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre :=
  E.chained.memory_chain

/-- `ipre`/`icur` are the LogUp accumulator pair on the public row. -/
theorem ipre_icur_are_pub_accumulators (pub : MemoryTable.Pub K) :
    pub.ipre = pub.ipre ∧ pub.icur = pub.icur :=
  ⟨rfl, rfl⟩

/-! ## E. `ForestExponentOrder` / `axisNat` not silently inhabited; `∀ a g` -/

/-- Uniqueness window is still `e < orderOf α` on committed template Nats,
not `∃ e, ts = α^e` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  rfl

/-- Generic fibre `Accepts` still takes `ForestExponentOrder`.  Production
`Accepts` at `honestCoin`, for `∀ a g`.  Not `∀ ω`. -/
theorem packageOf_fibre_accepts_still_takes_window
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
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

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
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

/-- `axisNat` stays named on the same two-field record. -/
theorem axisNat_stays_named
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- NMR address space remains the Nat-cast memory-table axis. -/
theorem nmr_axis_is_not_timestamp_power
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch121.censusRecordPremises_eta_still_five C

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch121.residualPremises_eta_still_four P

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch121.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField122
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

def substantiveFields122 : List ReviewedField122 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields122 : List ReviewedField122 := [.structural]

def residualFields122 : List ReviewedField122 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `timestampClosed` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields122.length = 11 ∧
      typeSummaryFields122.length = 1 ∧
      residualFields122 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields122.length = 2 ∧
      (substantiveFields122 ++ typeSummaryFields122 ++ residualFields122).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

variable [Fintype F] [DecidableEq F]

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

/-! ## F. F73: wrapping `α = 4`, `ts = 0` reconstructs `1`; extra remains -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete
open BuildableChips.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 fibre `α = 4` is nonzero.  Independent of the production wrapper. -/
theorem f73_alpha_eq_four :
    concreteExecution.cfg.challenges.α = (4 : K73cubic) :=
  rfl

theorem f73_alpha_ne_zero : (4 : K73cubic) ≠ 0 := by
  intro h0
  have hbase : (4 : F73) ≠ 0 := by decide
  exact hbase ((algebraMap F73 K73cubic).injective
    (by simpa [map_ofNat, map_zero] using h0))

/-- Wrapping witness: reconstructed power of `ts = 0` is `1`, and `0` is
not closed.  Not a claim that a live F73 row has `ts = 0`. -/
theorem f73_zero_not_timestampClosed :
    ¬ MemoryTimestampClosedAt concreteExecution.cfg.challenges.α 0 ∧
      concreteExecution.cfg.challenges.α ^
        timestampExp concreteExecution.cfg.challenges.α 0 = 1 := by
  rw [f73_alpha_eq_four]
  exact ⟨(reconstructed_power_ne_zero_timestamp f73_alpha_ne_zero).2.1,
    (reconstructed_power_ne_zero_timestamp f73_alpha_ne_zero).1⟩

theorem f73_reconstructed_one_ne_zero :
    (1 : K73cubic) ≠ 0 :=
  one_ne_zero

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

/-- Generic fibre `Accepts` on the F73 package still takes
`ForestExponentOrder`. -/
theorem f73_fibre_accepts_still_takes_window
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts hmore73 horder

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega data73
    GenericHonestArrays.Concrete.f73_char_gt_eleven inputs73Fold2
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField (lmb := lmb)

end Concrete

#print axioms timestampClosed_is_existence
#print axioms MemoryTimestampClosedAt_eq_TimestampClosedAt
#print axioms memoryMemRecKind_active_iff
#print axioms premises_timestampClosed_is_existence
#print axioms extra_applies_to_verify_child
#print axioms service_timestamp_is_closed
#print axioms recordPartition_is_read_root_emissions
#print axioms timestampClosed_of_root_response_record
#print axioms memoryRecordPremises_eta_still_two
#print axioms memoryNodesOf_takes_premises
#print axioms verify_child_emits_no_response
#print axioms verify_child_mem_not_in_own_responseRecords
#print axioms rawResponses_from_responseRecords
#print axioms derivedResponseIO_from_rawResponses
#print axioms semantic_responses_bridge_derivedResponseIO
#print axioms fmem_forces_state_agreement
#print axioms timestampClosed_of_identified_service_timestamps
#print axioms timestampExp_eq_zero_of_not_closed
#print axioms reconstructed_power_of_not_closed
#print axioms zero_not_closed_of_ne_zero
#print axioms reconstructed_power_ne_zero_timestamp
#print axioms wrapping_zero_is_extra_conclusion
#print axioms mem_forestVerifyTimestamps_is_reconstructed_power
#print axioms timestampExpAt_is_timestampExp
#print axioms execution_structural_intermediate_matching
#print axioms axisStructural_eta_omits_timestamp_closed
#print axioms execution_axisStructural_is_structural
#print axioms memory_chain_is_icur_ipre_handoff
#print axioms ipre_icur_are_pub_accumulators
#print axioms ForestExponentOrder_expands
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms axisNat_stays_named
#print axioms nmr_axis_is_not_timestamp_power
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_alpha_eq_four
#print axioms Concrete.f73_alpha_ne_zero
#print axioms Concrete.f73_zero_not_timestampClosed
#print axioms Concrete.f73_reconstructed_one_ne_zero
#print axioms Concrete.f73_fibre_accepts_still_takes_window
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch122
