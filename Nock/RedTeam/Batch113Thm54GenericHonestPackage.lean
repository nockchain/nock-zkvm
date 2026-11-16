import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch112Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
**Status of the cite only.  Four
declaration cites here read the paper for the slot base case `\(1, n_1) = n_1`.  **The range cite `1288-1291` in
the paper frame above does contain the base case and is NOT wrong** — only the component cite
`1289` is.  The claim is unaffected.

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Lean `CensusRecordPremises.slotSemantics` is not the
paper `/` definition.  The paper operator is `Noun.slot` (`/(1,n)=n`,
children `2·axis` / `2·axis+1`, the paper).  The named extra is
`Noun.slot` on reconstructed OP0/OP9 compute-skeleton rows
(`ServedLookupBridge.SkeletonSlotSemantics`).  `needs.served` is a
`ServedLookup` of some nouns.  The paper base case inhabits that lookup at
axis `1` for every noun.  Assembled record equations are root/child
identities, not `/`.  NMR `axisNat` is a
memory-table Nat-cast, not a compute-skeleton
`/` fact.  The missing hypothesis is identification of the served lookup
with the reconstructed skeleton's subject, `mr2`/`mr3` axis, and child.
A real OP0 row with subject `.atom 0`, `mr2.axis = 2`, evaluation
`.atom 1` has record equations, has the axis-1 base-case lookup, and fails
the extra: `Noun.slot 2 (.atom 0) = none`.  Slot predicates are not
weakened.  Census extras stay five.  `Inputs` stays named.  Accounting
remains `11+1+2`.  The extra is not rounded into a paper-`/` or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch113

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

/-! ## A. Lean extra ≠ paper `/` definition -/

/-- Paper `/` base case: `/(1,n_1)=n_1` for every noun.  This is the
operator, not the census extra -/
theorem paper_slash_base (n : Noun) : Noun.slot 1 n = some n := by
  simp [Noun.slot]

/-- Paper `/` left child: axis `2` of a cell is the head. -/
theorem paper_slash_left (l r : Noun) :
    Noun.slot 2 (.cell l r) = some l := by
  simp [Noun.slot]

/-- Paper `/` right child: axis `3` of a cell is the tail. -/
theorem paper_slash_right (l r : Noun) :
    Noun.slot 3 (.cell l r) = some r := by
  simp [Noun.slot]

/-- Axis `2` of an atom is `none`.  Atoms have no children. -/
theorem paper_slash_atom_axis_two (a : ℕ) :
    Noun.slot 2 (.atom a) = none := by
  simp [Noun.slot]

/-- The named extra expands to the OP0/OP9 `/` facts on a compute-skeleton
row, not `True` and not the operator definition itself. -/
theorem slotSemantics_is_noun_slot_on_skeleton
    (s : ComputeRowSkeleton)
    (h : ServedLookupBridge.SkeletonSlotSemantics s) :
    (s.state = .s0 →
      Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject =
        some s.evaluation) ∧
      (s.state = .s9 →
        Noun.slot (P8Census.skeletonMemoryAxis s 2)
          (P8Census.skeletonSubformula s 0 .result) =
            some (P8Census.skeletonSubformula s 1 .formula)) :=
  ⟨h.s0_slot, h.s9_slot⟩

/-- Consumed extra: `CensusRecordPremises.slotSemantics` is that skeleton
predicate on assembled reconstructed rows -/
theorem census_slotSemantics_is_assembled_skeleton_rows
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  C.slotSemantics

/-- Slot predicates were not rewritten: the naming is still an `Iff` with
the served fields -/
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
  ServedLookupBridge.skeletonSlotSemantics_iff_served s

/-- Recognizer translation is still `ServedLookup ↔ Noun.slot`.  Language
change, not a weakening -/
theorem served_lookup_still_iff_noun_slot (a : ℕ) (root child : Noun) :
    GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun root 1) a child ↔
      Noun.slot a root = some child :=
  RecognizerCompleteness.servedLookup_iff_slot a root child

/-! ## B. Missing identification is extra, not `True` -/

/-- Paper base case inhabits a `ServedLookup` at axis `1` for every noun,
without identifying a reconstructed `mr2` axis or evaluation. -/
theorem served_lookup_of_axis_one (n : Noun) :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun n 1) 1 n :=
  RecognizerCompleteness.servedLookup_root n

/-- `needs.served` at OP0 is a lookup of *some* nouns, not the reconstructed
skeleton's subject / `mr2` axis / evaluation -/
theorem served_lookup_of_s0_is_some_nouns
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (h : row.1 = .s0) :
    ∃ lookup ∈ data.needs.served,
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun lookup.root 1) lookup.axis lookup.child :=
  served_lookup_of_s0_needs data h

/-- Independent reconstruction: a served lookup inhabits OP0
`SkeletonSlotSemantics` only after identification with the reconstructed
skeleton -/
theorem slotSemantics_of_s0_served_and_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s0) (hroot : lookup.root = s.subject)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 1)
    (hchild : lookup.child = s.evaluation) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  ServedLookupBridge.skeletonSlotSemantics_of_served
    (fun _ => hroot ▸ haxis ▸ hchild ▸ lookup.served)
    (fun h9 => nomatch hstate.symm.trans h9)

/-- OP9 analogue of the same missing identification -/
theorem slotSemantics_of_s9_served_and_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s9)
    (hroot : lookup.root = P8Census.skeletonSubformula s 0 .result)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 2)
    (hchild : lookup.child = P8Census.skeletonSubformula s 1 .formula) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  ServedLookupBridge.skeletonSlotSemantics_of_served
    (fun h0 => nomatch hstate.symm.trans h0)
    (fun _ => hroot ▸ haxis ▸ hchild ▸ lookup.served)

/-- Record equations are root/child identities, not `/`. -/
theorem recordEquations_are_root_child_identities
    (s : ComputeRowSkeleton)
    (h : ServedLookupBridge.SkeletonRecordEquations s) :
    (∀ hs0 : s.state = .s0,
      let mr := s.memoryRecord (1 : Fin 3)
        (by simp [hs0, Nock.Framework.recordCount])
      mr.root = s.subject ∧ mr.child = s.evaluation) ∧
      (∀ hs9 : s.state = .s9,
        let mr := s.memoryRecord (2 : Fin 3)
          (by simp [hs9, Nock.Framework.recordCount])
        mr.root = P8Census.skeletonSubformula s 0 .result ∧
          mr.child = P8Census.skeletonSubformula s 1 .formula) :=
  ⟨h.s0_record, h.s9_record⟩

/-- NMR `axisNat` is a live memory-table address as a Nat-cast into the
field.  It does not mention `Noun.slot` or a compute-skeleton row. -/
theorem axisNat_is_memory_table_nat_cast
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- `censusAssemblyOf` still copies `slotSemantics` from the named extra. -/
theorem censusAssemblyOf_still_copies_slotSemantics
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).slotSemantics = C.slotSemantics :=
  rfl

/-! ## C. Non-vacuous OP0 witness: records and axis-1 hold, extra fails -/

/-- Explicit OP0 row: subject `.atom 0`, `mr2.axis = 2`, evaluation
`.atom 1` -/
def failRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 2)
  evaluation := .atom 1
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ =>
    if (i : ℕ) = 1 then
      ⟨.atom 0, .atom 1, 2⟩
    else
      ⟨.atom 0, .atom 2, 3⟩

theorem failRow_axis :
    P8Census.skeletonMemoryAxis failRow 1 = 2 := by
  simp [P8Census.skeletonMemoryAxis, failRow, Nock.Framework.recordCount]

/-- Paper axis `1` is not this row's `mr2` axis -/
theorem paper_base_axis_ne_fail_row_axis :
    1 ≠ P8Census.skeletonMemoryAxis failRow 1 := by
  rw [failRow_axis]
  decide

theorem failRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations failRow where
  s0_record := by
    intro _
    simp [failRow]
  s9_record := by
    intro h
    cases h

/-- `/[2, atom 0]` is `none`, so it is not `some (atom 1)`. -/
theorem failRow_slot_ne :
    Noun.slot (P8Census.skeletonMemoryAxis failRow 1) failRow.subject ≠
      some failRow.evaluation := by
  rw [failRow_axis]
  simp [failRow, Noun.slot]

theorem failRow_slot_eq_none :
    Noun.slot 2 failRow.subject = none := by
  simp [failRow, Noun.slot]

/-- Same subject still satisfies the paper `/(1,n)=n` lookup. -/
theorem failRow_slot_one :
    Noun.slot 1 failRow.subject = some failRow.subject :=
  paper_slash_base _

theorem slotSemantics_fails_on_failRow :
    ¬ ServedLookupBridge.SkeletonSlotSemantics failRow := by
  intro h
  exact failRow_slot_ne (h.s0_slot rfl)

theorem served_lookup_axis_one_holds_on_failRow :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun failRow.subject 1) 1 failRow.subject :=
  served_lookup_of_axis_one _

/-- Combined: record equations hold, the paper axis-1 base case holds, and
the named extra fails.  The missing identification is therefore extra. -/
theorem slotSemantics_does_not_follow_from_records_or_axis_one :
    ServedLookupBridge.SkeletonRecordEquations failRow ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun failRow.subject 1) 1
        failRow.subject ∧
      Noun.slot 1 failRow.subject = some failRow.subject ∧
      Noun.slot 2 failRow.subject = none ∧
      ¬ ServedLookupBridge.SkeletonSlotSemantics failRow :=
  ⟨failRow_recordEquations,
    served_lookup_axis_one_holds_on_failRow,
    failRow_slot_one,
    failRow_slot_eq_none,
    slotSemantics_fails_on_failRow⟩

/-- Concrete nonempty skeleton whose unique compute row is that OP0 atom.
The extra's `∀ s ∈ computeSkeletonRows` quantifier therefore fails. -/
def failSkeleton : SemanticSkeleton where
  computeTree := .node failRow []
  memoryForest := []

theorem failSkeleton_computeRows :
    computeSkeletonRows failSkeleton = [failRow] := by
  unfold computeSkeletonRows failSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem slotSemantics_forall_fails_on_failSkeleton :
    ¬ ∀ s ∈ computeSkeletonRows failSkeleton,
        ServedLookupBridge.SkeletonSlotSemantics s := by
  intro h
  rw [failSkeleton_computeRows] at h
  exact slotSemantics_fails_on_failRow (h _ (by simp))

/-- The prover's named witness is the same predicate-separation: records
and axis-1 hold, extra fails -/
theorem prover_witness_agrees :
    ServedLookupBridge.SkeletonRecordEquations s0SlotFailRow ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s0SlotFailRow.subject 1) 1
        s0SlotFailRow.subject ∧
      ¬ ServedLookupBridge.SkeletonSlotSemantics s0SlotFailRow :=
  GenericHonestData.slotSemantics_does_not_follow_from_records_or_axis_one

/-! ## D. NMR axis is not re-litigated; no silent inhabit of another extra -/

/-- NMR address space remains the Nat-cast memory-table axis. -/
theorem nmr_axis_is_not_compute_slot
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

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

variable [Fintype F] [DecidableEq F]

/-! ## E. -/

inductive ReviewedField113
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

def substantiveFields113 : List ReviewedField113 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields113 : List ReviewedField113 := [.structural]

def residualFields113 : List ReviewedField113 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Leaving `slotSemantics` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields113.length = 11 ∧
      typeSummaryFields113.length = 1 ∧
      residualFields113 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields113.length = 2 ∧
      (substantiveFields113 ++ typeSummaryFields113 ++ residualFields113).Nodup ∧
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

#print axioms paper_slash_base
#print axioms paper_slash_left
#print axioms paper_slash_right
#print axioms paper_slash_atom_axis_two
#print axioms slotSemantics_is_noun_slot_on_skeleton
#print axioms census_slotSemantics_is_assembled_skeleton_rows
#print axioms slot_predicates_still_iff_served
#print axioms served_lookup_still_iff_noun_slot
#print axioms served_lookup_of_axis_one
#print axioms served_lookup_of_s0_is_some_nouns
#print axioms slotSemantics_of_s0_served_and_identification
#print axioms slotSemantics_of_s9_served_and_identification
#print axioms recordEquations_are_root_child_identities
#print axioms axisNat_is_memory_table_nat_cast
#print axioms censusAssemblyOf_still_copies_slotSemantics
#print axioms failRow_axis
#print axioms paper_base_axis_ne_fail_row_axis
#print axioms failRow_recordEquations
#print axioms failRow_slot_ne
#print axioms failRow_slot_eq_none
#print axioms failRow_slot_one
#print axioms slotSemantics_fails_on_failRow
#print axioms served_lookup_axis_one_holds_on_failRow
#print axioms slotSemantics_does_not_follow_from_records_or_axis_one
#print axioms failSkeleton_computeRows
#print axioms slotSemantics_forall_fails_on_failSkeleton
#print axioms prover_witness_agrees
#print axioms nmr_axis_is_not_compute_slot
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms dataOfCensus_still_requires_C
#print axioms packageOf_still_takes_named_Inputs
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_data_still_forces_q_pin
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_is_noun_slot
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_does_not_follow_from_records_or_axis_one
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch113
