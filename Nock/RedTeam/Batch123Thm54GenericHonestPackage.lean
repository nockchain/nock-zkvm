import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch122Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.MemoryTable
import Nock.NockVM
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
`Def:NMR` the paper; lookup validity the paper; NMR CORE
the paper; per-node doubling the paper; live
kinds the paper; joint NockVMROM the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `MemoryRecordPremises.axisNat` is inhabited from
already-held NMR Nat-cast on assembled memory rows.  The extra is
`∃ n, mem.axis = (n : K)` on every live `read_root` and `verify_child`
row.  That is Def:NMR address-space Nat-cast, not a weaker Prop.
`read_root` uses `recordPartition` / `Service.realization.axis_realizes`.
`verify_child` uses committed `vaxis = Relaxis` on `exactAxisTree`, and
`Relaxis` is a Nat-cast of the paper doubling.  The inhabit theorem
takes only `E`, not `MemoryRecordPremises` / `C`.  `timestampClosed`,
`axisAtoms`, and `ForestExponentOrder` stay named.  Accounting remains
`11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch123

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
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.ServedMemoryTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Extra is Def:NMR Nat-cast on both live kinds, not a weaker Prop -/

/-- Lean extra: live memory-table `mem.axis` is a Nat-cast. -/
theorem axisNat_extra_is_nat_cast
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- Live rows are exactly `read_root` and `verify_child`.
Independent of the production wrapper -/
theorem memoryMemRecKind_active_iff (s : MemoryTable.MState) :
    memoryMemRecKind s = .active ↔ s = .read_root ∨ s = .verify_child :=
  Batch122.memoryMemRecKind_active_iff s

/-- Named extra quantifies over every active row, hence both live kinds. -/
theorem extra_applies_to_read_root
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat i (by simp [memoryMemRecKind, h])

theorem extra_applies_to_verify_child
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat i (by simp [memoryMemRecKind, h])

/-- Topological `Relaxis` is the paper doubling with a leading `1`.
Independent unfold -/
theorem Relaxis_at_read_is_doubling (e e' : ℕ) (c : MTree K) :
    Relaxis e (MTree.read e' c) =
      if e' = e then vaddr e c + (2 : K) ^ vdep e c else Relaxis e c :=
  rfl

/-- Committed `vaxis` at a verify node is the node's `address` column.
Independent unfold -/
theorem vaxis_at_verify_is_committed_address (e e' : ℕ) (a : K) (c : MTree K) :
    vaxis e (MTree.verify e' a c) = if e' = e then a else vaxis e c :=
  rfl

/-- Independent: `vaddr` is always a Nat-cast of the binary path. -/
theorem independent_vaddr_is_nat_cast (e : ℕ) :
    ∀ t : MTree K, ∃ n : ℕ, vaddr e t = (n : K) := by
  intro t
  induction t with
  | halt => exact ⟨0, by simp [vaddr]⟩
  | decompose l r ihl ihr =>
      by_cases hvl : verifyCount e l = 1
      · simpa [vaddr, hvl] using ihl
      · obtain ⟨n, hn⟩ := ihr
        refine ⟨n + 2 ^ vdep e r, ?_⟩
        simp [vaddr, hvl, hn, Nat.cast_add, Nat.cast_pow]
  | read _e c ih => simpa [vaddr] using ih
  | verify e' _a c ih =>
      by_cases he : e' = e
      · exact ⟨0, by simp [vaddr, he]⟩
      · simpa [vaddr, he] using ih

/-- Independent: `Relaxis` is always a Nat-cast of that doubling.
Same object as Def:NMR address space -/
theorem independent_relaxis_is_nat_cast (e : ℕ) :
    ∀ t : MTree K, ∃ n : ℕ, Relaxis e t = (n : K) := by
  intro t
  induction t with
  | halt => exact ⟨0, by simp [Relaxis]⟩
  | decompose l r ihl ihr =>
      by_cases hrl : readCount e l = 1
      · simpa [Relaxis, hrl] using ihl
      · simpa [Relaxis, hrl] using ihr
  | read e' c ih =>
      by_cases he : e' = e
      · obtain ⟨n, hn⟩ := independent_vaddr_is_nat_cast e c
        refine ⟨n + 2 ^ vdep e c, ?_⟩
        simp [Relaxis, he, hn, Nat.cast_add, Nat.cast_pow]
      · simpa [Relaxis, he] using ih
  | verify _e' _a c ih => simpa [Relaxis] using ih

/-- Production `relaxis_is_nat_cast` is that same fact. -/
theorem production_relaxis_agrees (e : ℕ) (t : MTree K) :
    (∃ n : ℕ, Relaxis e t = (n : K)) :=
  GenericHonestData.relaxis_is_nat_cast e t

/-! ## B. Inhabit is real on assembled rows: Service / Relaxis, not `M` / `C` -/

/-- Independent: a served record's `axis` is already a Nat-cast.
Does not mention `MemoryRecordPremises` -/
theorem independent_service_axis_is_nat_cast
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : Service cfg exec) :
    ∃ n : ℕ, s.record.axis = (n : K) :=
  ⟨s.axis, s.realization.axis_realizes⟩

/-- Identification with a service record's axis inhabits the extra on that
row.  Not `True`, and not a copy from `M.axisNat` -/
theorem extra_of_identified_service_axis
    {E : BuildableNockExecution F K} {i : Fin E.cfg.memRows}
    {s : Service E.cfg E.execA}
    (h : (E.execA.memoryRowAt i).2.2.mem.axis = s.record.axis) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  ⟨s.axis, h.trans s.realization.axis_realizes⟩

/-- Calc shape for `verify_child`: committed column, walk validity, Nat-cast.
Does not mention `MemoryRecordPremises` -/
theorem extra_of_committed_relaxis {axis : K} {e : ℕ} {t : MTree K}
    (hvaxis : axis = vaxis e t) (hval : vaxis e t = Relaxis e t) :
    ∃ n : ℕ, axis = (n : K) := by
  obtain ⟨n, hn⟩ := independent_relaxis_is_nat_cast e t
  exact ⟨n, hvaxis.trans (hval.trans hn)⟩

/-- Independent `read_root` inhabit on assembled memory rows.  Uses
`recordPartition` and `axis_realizes`, not `M.axisNat`. -/
theorem independent_axisNat_of_read_root (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root)
    (hver : (E.exec.memoryRowAt i).2.2.ver = true) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_read_root E i
    (by simpa [GenericHonestData.exec_memoryRowAt_encode] using h)
    (by simpa [GenericHonestData.exec_memoryRowAt_encode] using hver)

/-- Production `verify_child` inhabit: assembled `mem.axis` equals walk
`vaxis = Relaxis`, which is a Nat-cast.  Type takes only `E`. -/
theorem independent_axisNat_of_verify_child (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_verify_child E i
    (by simpa [GenericHonestData.exec_memoryRowAt_encode] using h)

/-- Both live kinds, from `E` under honest `ver`.  No `MemoryRecordPremises` binder. -/
theorem independent_axisNat_of_execution (E : BuildableNockExecution F K)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_execution E honestVer

/-- Honest filler copies `axisNat` from that theorem, not from
an input `MemoryRecordPremises` or from `C` -/
theorem filler_axisNat_is_execution_not_copied
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (GenericHonestData.memoryRecordPremises_of_timestampClosed E
        timestampClosed honestVer).axisNat =
      GenericHonestData.axisNat_of_execution E honestVer :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed_fills_axisNat
    E timestampClosed honestVer

/-- Inverse-BFS reconstruction still *consumes* the extra; it does not
inhabit it -/
theorem memoryNodesOf_takes_premises
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    memoryNodesOf E M = memoryForestOf E M :=
  Batch122.memoryNodesOf_takes_premises E M

/-- Assembled skeleton axis still reads `M.axisNat`.  Reconstruction is
not a silent inhabit -/
theorem memoryMemRecSkel_consumes_axisNat
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    (memoryMemRecSkel E M i hact).axis = (M.axisNat i hact).choose :=
  rfl

/-- Census extras do not contain `axisNat` -/
theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch122.censusRecordPremises_eta_still_five C

/-- `dataOfRecord` still takes a `MemoryRecordPremises` value.  Honest
assembly may fill `axisNat` first -/
theorem dataOfRecord_still_takes_premises
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) (memoryNodesOf E M))
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    dataOfRecord E P M C hln =
      dataOf E P (memoryAssemblyOf E M) C hln :=
  rfl

/-! ## C. `timestampClosed` / `axisAtoms` / `ForestExponentOrder` stay named -/

/-- Two-field eta is unchanged -/
theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch122.memoryRecordPremises_eta_still_two M

/-- Filler still takes live `ts = α^e` as a named input. -/
theorem filler_still_takes_timestampClosed
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (GenericHonestData.memoryRecordPremises_of_timestampClosed E
        timestampClosed honestVer).timestampClosed =
      timestampClosed :=
  rfl

/-- After filling `axisNat`, `timestampClosed` remains the named half. -/
theorem timestampClosed_stays_named
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  M.timestampClosed

/-- Compute OP0/OP9 formula-tail extra is a different object from NMR
memory-table Nat-cast -/
theorem axisAtoms_is_op0_op9_formula_tail
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row} :
    AxisAtomPremises data =
      ((row.1 = .s0 → ∃ k, data.root.tail = Noun.atom k) ∧
        (row.1 = .s9 → ∃ k, decompNoun data .f_th = Noun.atom k)) :=
  rfl

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch122.residualPremises_eta_still_four P

/-- Uniqueness window is still `e < orderOf α`, not Nat-cast existence. -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch122.ForestExponentOrder_expands E α

/-- Generic fibre `Accepts` still takes `ForestExponentOrder`.
Production `Accepts` at `honestCoin`, for `∀ a g`.  Not `∀ ω`. -/
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

/-! ## D. -/

/-- NMR address space remains the Nat-cast memory-table axis.  `timestampClosed` stays the other field. -/
theorem nmr_axis_is_nat_cast_not_missing
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨independent_axisNat_of_execution E M.honestVer, M.timestampClosed⟩

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
  Batch122.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField123
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

def substantiveFields123 : List ReviewedField123 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields123 : List ReviewedField123 := [.structural]

def residualFields123 : List ReviewedField123 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Inhabiting `axisNat` is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields123.length = 11 ∧
      typeSummaryFields123.length = 1 ∧
      residualFields123 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields123.length = 2 ∧
      (substantiveFields123 ++ typeSummaryFields123 ++ residualFields123).Nodup ∧
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

/-! ## E. F73: inhabit fires on a real assembled execution; extras remain -/

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

/-- F73 assembled rows inhabit `axisNat` from `E` alone.
Not a copy from `MemoryRecordPremises` -/
theorem f73_axisNat_of_execution :
    ∀ i : Fin concreteExecution.cfg.memRows,
      memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (concreteExecution.execA.memoryRowAt i).2.2.mem.axis =
          (n : K73cubic) :=
  independent_axisNat_of_execution concreteExecution
    BuildableChips.Concrete.concrete_honest_ver

/-- Filler on F73 still requires named `timestampClosed`. -/
theorem f73_filler_still_takes_timestampClosed
    (timestampClosed :
      ∀ i : Fin concreteExecution.cfg.memRows,
        memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
            (concreteExecution.exec.memoryRowAt i).2.2.mem.ts) :
    MemoryRecordPremises concreteExecution :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed
    concreteExecution timestampClosed BuildableChips.Concrete.concrete_honest_ver

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

#print axioms axisNat_extra_is_nat_cast
#print axioms memoryMemRecKind_active_iff
#print axioms extra_applies_to_read_root
#print axioms extra_applies_to_verify_child
#print axioms Relaxis_at_read_is_doubling
#print axioms vaxis_at_verify_is_committed_address
#print axioms independent_vaddr_is_nat_cast
#print axioms independent_relaxis_is_nat_cast
#print axioms production_relaxis_agrees
#print axioms independent_service_axis_is_nat_cast
#print axioms extra_of_identified_service_axis
#print axioms extra_of_committed_relaxis
#print axioms independent_axisNat_of_read_root
#print axioms independent_axisNat_of_verify_child
#print axioms independent_axisNat_of_execution
#print axioms filler_axisNat_is_execution_not_copied
#print axioms memoryNodesOf_takes_premises
#print axioms memoryMemRecSkel_consumes_axisNat
#print axioms censusRecordPremises_eta_still_five
#print axioms dataOfRecord_still_takes_premises
#print axioms memoryRecordPremises_eta_still_two
#print axioms filler_still_takes_timestampClosed
#print axioms timestampClosed_stays_named
#print axioms axisAtoms_is_op0_op9_formula_tail
#print axioms residualPremises_eta_still_four
#print axioms ForestExponentOrder_expands
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms nmr_axis_is_nat_cast_not_missing
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_axisNat_of_execution
#print axioms Concrete.f73_filler_still_takes_timestampClosed
#print axioms Concrete.f73_fibre_accepts_still_takes_window
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch123
