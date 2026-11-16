/-
  Nock/RedTeam/Batch12Thm54Independent.lean

  The countermodels below compile against the exact public classes used by
  `NockVMROM_Thm54_structural`.

  Paper authority:
  * canonical RAP: the paper
  * opcode/memory one-hot conditions 1--5: the paper
  * traversability bijections: the paper
  * Theorem 5.4: the paper.

  No result below says the underlying table or walk theorems are false.  They show that the
  assembled property surfaces omit load-bearing links/clauses, so inhabiting the bundle does not
  by itself establish the paper-shaped conjunction currently claimed for it.
-/
import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Asymptotic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace Nock.RedTeam

open Nock Nock.Framework Nock.NockVMROM

instance b12_fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## S1 / core language: the IO witness is not connected to either table fold -/

/-- **Core-language counterexample.**  Empty compute and memory tables accept
    *any* self-matched semantic record as their IO witness.  `ComputeTableAccepts` does not consume
    `progIO`, and `MemoryTableAccepts` does not consume `memIO`; only the standalone `LmIO` conjunct
    sees them.  Thus the Lean recognizer does not establish that `W_comp^IO`/`W_mem^IO` are the IO
    columns of the same table witnesses, which the paper threads as arguments to `V_comp`/`V_mem`. -/
theorem b12_s1_empty_tables_accept_arbitrary_self_io
    (F K : Type) [Field F] [Field K] (r : (nmrMEF F K).Rec) :
    accepts 1 (⟨[], []⟩ : Stmt F K) (⟨[], [r], [r]⟩ : Wit F K) := by
  refine ⟨List.Forall₂.nil, ?_, ?_⟩
  · intro row hrow
    simp at hrow
  · exact ⟨⟨le_rfl, le_rfl⟩, [r], le_rfl, List.nodup_singleton r,
      fun _ => Iff.rfl, List.Perm.refl _⟩

/-- The language is definitionally independent of the purported NMR encoding points `α,β`.
    This is consistent with the disclosed semantic-`nmrMEF` repair, but confirms that the claimed
    core recognizer itself contains no `α,β` record-encoding condition. -/
theorem b12_s1_alpha_beta_phantom
    (F K : Type) [Field F] [Field K] (α₁ β₁ α₂ β₂ : K) (x : Stmt F K) :
    Language (Tag F K α₁ β₁ 1) x ↔ Language (Tag F K α₂ β₂ 1) x :=
  Iff.rfl

/-! ## S2: `HasCanonicalRAP` can be self-justifying and its stored RAP is not the proved RAP -/

/-- **S2 countermodel.**  The public class can be inhabited on the exact
    NockVMROM tag with `progAccepts = progSatisfiable = True` and
    `memAccepts = memSatisfiable = True`.  It does not require the S1 separation, common RAP
    parameters, shared witness columns, or an encoding into the stored `Rprog`/`Rmem`. -/
@[reducible] noncomputable def b12_s2_self_justifying :
    HasCanonicalRAP (Tag ℚ ℚ 0 1 1) (nmrMEF ℚ ℚ) ℚ where
  Rprog := (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rprog
  Rmem := (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rmem
  ProgProblem := Unit
  MemProblem := Unit
  progAccepts := fun _ => True
  progSatisfiable := fun _ => True
  memAccepts := fun _ => True
  memSatisfiable := fun _ => True
  compute_iff := fun _ => Iff.rfl
  memory_iff := fun _ => Iff.rfl

/-- The actual S2 instance stores an empty-domain, unit-parameter decoration.  Its load-bearing
    `progSatisfiable` predicate constructs a different, problem-indexed RAP, so the stored
    `Rprog` is not the RAP occurring in `compute_iff`. -/
theorem b12_s2_stored_Rprog_domain_empty :
    (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rprog.H = ∅ :=
  rfl

/-! ## S3: the replacement class omits paper conditions 2, 4, and 5 -/

/-- **S3 vacuity countermodel.**  `OpcodeMemoryOneHot... 10 3` is inhabited
    with an empty row type.  Every current field is then vacuous.  In particular, the class has no
    memory-row selector/table, no IO records, and no fields expressing paper condition 2 (one
    memory record per memory row), condition 4's zero-padding, or condition 5
    (`IO_mem ⊆ x_mem`). -/
@[reducible] noncomputable def b12_s3_empty_row_countermodel :
    @OpcodeMemoryOneHot (Tag ℚ ℚ 0 1 1) _ (nmrMEF ℚ ℚ) ℚ _ 10 3
      (nock_uniqueMES ℚ ℚ 0 1 1) where
  Row := Empty
  numericSelector := Empty.elim
  structuralSelector := Empty.elim
  recordCount := Empty.elim
  numeric_boolean := fun row => Empty.elim row
  structural_boolean := fun row => Empty.elim row
  exactly_one_action_per_compute_row := fun row => Empty.elim row
  record_arity_le := fun row => Empty.elim row
  record_pos := fun row => Empty.elim row

/-! ## S4: no paper bijection, and the claimed reverse inclusion does not mention acceptance -/

/-- The actual S1 compute language accepts the empty compute table (the fold is `Forall₂.nil`). -/
theorem b12_s4_empty_compute_accepted :
    (nock_uniqueMES ℚ ℚ 0 1 1).computeAccepts [] ([], []) [] := by
  exact ⟨List.Forall₂.nil, rfl⟩

/-- But every value of the S4 `computeReadout` is a singleton row.  Hence an actually accepted
    compute-language element is outside the readout image.  The `IsTraversable` class still exists
    because `recognized_complete_compute` never quantifies over `S.computeAccepts`; it only
    reconstructs rows already assumed to satisfy `Fcomp`.  This refutes the documentation claim
    that the current fields establish the paper's bijection. -/
theorem b12_s4_accepted_not_in_readout :
    ∃ (ps : (nock_uniqueMES ℚ ℚ 0 1 1).ProgStatement)
      (pw : (nock_uniqueMES ℚ ℚ 0 1 1).ProgWitness)
      (io : (nock_uniqueMES ℚ ℚ 0 1 1).ProgIO),
      (nock_uniqueMES ℚ ℚ 0 1 1).computeAccepts ps pw io ∧
      ∀ lbl : (nock_traversalModel ℚ ℚ 0 1 1).ComputeLabel,
        ((nock_isTraversable ℚ ℚ 0 1 1).computeReadout lbl).1 ≠ ps := by
  refine ⟨[], ([], []), [], b12_s4_empty_compute_accepted, ?_⟩
  intro lbl
  change [((lbl.2.1, lbl.2.2.1))] ≠ []
  simp

/-- The concrete traversal model declares one memory factor, while the bundled completeness field
    separately quantifies an arbitrary forest-root count `kroots`.  The two counts are not tied. -/
theorem b12_s4_declares_one_memory_root :
    (nock_traversalModel ℚ ℚ 0 1 1).memRoots = 1 :=
  rfl

/-! ## S5: the class is not linked to either canonical RAP or shared witness correctness -/

/-- **S5 countermodel.**  The exact NockVMROM tag admits a two-RAP model with no
    RAPs at all, zero-vs-zero bounds, and `rapIOAccepts := True`.  The class only asks that this
    arbitrary relation be inhabited; it has no `HasCanonicalRAP` input and no shared-IO iff tying
    the two actual RAP witnesses together. -/
def b12_s5_unrelated_model :
    TwoRAPVerificationModel (Tag ℚ ℚ 0 1 1) (nmrMEF ℚ ℚ) ℚ where
  ComputeTrial := Unit
  MemoryTrial := Unit
  IOWitness := Unit
  computeBadProbability := fun _ => 0
  memoryBadProbability := fun _ => 0
  computeBound := fun _ => 0
  memoryBound := fun _ => 0
  rapIOAccepts := fun _ => True
  ioBound := 0

/-- The unrelated S5 model satisfies the public property class. -/
@[reducible] def b12_s5_unrelated_model_verifies :
    HasTwoRAPVerification (Tag ℚ ℚ 0 1 1) (nmrMEF ℚ ℚ) ℚ b12_s5_unrelated_model where
  compute_sound := fun _ => le_rfl
  memory_sound := fun _ => le_rfl
  shared_io := ⟨(), trivial⟩

/-! ## S6: the bundled completeness model covers only the compute RAP -/

/-- The Nock S6 model's entire problem space is `ComputeProblem`; no memory problem or shared IO
    occurs in the type, although Theorem 5.4 claims perfect completeness for both `N` opcodes and
    `L` memory records. -/
theorem b12_s6_problem_is_compute_only :
    (nockCompletenessModel ℚ ℚ 0 1 1).Problem = ComputeProblem ℚ :=
  rfl

/-- Its accepted predicate is exactly the compute-table fold, with no memory or IO conjunct. -/
theorem b12_s6_accepted_is_compute_only (p : ComputeProblem ℚ) :
    (nockCompletenessModel ℚ ℚ 0 1 1).accepted p ↔
      ∀ k, ComputeTable.Vcomp (p.inp k) (p.pub k) (p.dec k) :=
  Iff.rfl

/-! ## S7: the concrete model is a generic sum of walk bounds, not NockVMROM verification -/

/-- The actual fixed-field S7 bad probability and bound are definitionally independent of the
    Nock encoding points `α,β` and IO bound `Ksz`.  The model contains only two generic walk trials;
    it has no NockVMROM acceptance event, shared-IO failure, RLC set-equality trial, or NPR
    collision-table event. -/
theorem b12_s7_tag_parameters_phantom
    (α₁ β₁ α₂ β₂ : ZMod 7) (Ksz₁ Ksz₂ : ℕ)
    (t : ComputeWalkTrial (ZMod 7) × ForestWalkTrial (ZMod 7)) :
    (nockConcreteSoundness (ZMod 7) (ZMod 7) α₁ β₁ Ksz₁).badProbability t =
        (nockConcreteSoundness (ZMod 7) (ZMod 7) α₂ β₂ Ksz₂).badProbability t ∧
      (nockConcreteSoundness (ZMod 7) (ZMod 7) α₁ β₁ Ksz₁).bound t =
        (nockConcreteSoundness (ZMod 7) (ZMod 7) α₂ β₂ Ksz₂).bound t :=
  ⟨rfl, rfl⟩

/-! ## Asymptotic S7: the concrete characteristic-two family is incompatible with the AIR -/

/-- `computeAIR_sound_free` requires that casts of naturals through `11` do not collapse to `1`.
    The claimed concrete family starts with `GF(2)`, where `3 = 1`, so it cannot instantiate that
    Nock AIR soundness hypothesis.  The cardinality-growth theorem is valid; its connection to the
    concrete Nock soundness theorem is not. -/
theorem b12_asymptotic_family_fails_compute_hchar :
    ¬ (∀ m : ℕ, m ≤ 11 →
      (m : GaloisField 2 1) = 1 → m = 1) := by
  intro h
  have hcast : (3 : GaloisField 2 1) = 1 := by
    have : CharP (GaloisField 2 1) 2 := inferInstance
    reduce_mod_char!
  have h3 := h 3 (by omega) hcast
  omega

/-! ## S8: the bundled cost property does not tie costs to the VM or AIR -/

/-- A VM that rejects every statement. -/
structure B12RejectVM : Type

instance : VMSystem B12RejectVM where
  Statement := Unit
  Witness := Unit
  accepts := fun _ _ => False

/-- The rejecting VM satisfies `HasCostModel` for the
    Nock reified numbers, because the class checks only arithmetic internal to `cost`. -/
@[reducible] def b12_s8_reject_vm_costed : HasCostModel B12RejectVM reifiedNockCost where
  compMaxDegree_eq_four := rfl
  memMaxDegree_eq_four := rfl
  memory_fewer_constraints := by decide
  memory_fewer_deg4 := by decide

/-! ## S8 companion: `paperNockCost` transcribes the wrong paper layer -/

/-- The actual Theorem-5.4 `+IO` figures at `e = 3`. -/
theorem b12_thm54_final_cost_figures :
    Nock.NockVM.comp_io_columns 3 = 199 ∧
      Nock.NockVM.mem_io_columns 3 = 196 ∧
      Nock.NockVM.comp_io_deg4_gates 3 = 87 ∧
      Nock.NockVM.mem_io_deg4_gates 3 = 88 := by
  decide

/-- `paperNockCost` is not a transcription of those final Theorem-5.4 figures. -/
theorem b12_paperNockCost_is_not_thm54_final :
    paperNockCost.compCols ≠ Nock.NockVM.comp_io_columns 3 ∧
      paperNockCost.memCols ≠ Nock.NockVM.mem_io_columns 3 ∧
      paperNockCost.compDeg4 ≠ Nock.NockVM.comp_io_deg4_gates 3 ∧
      paperNockCost.memDeg4 ≠ Nock.NockVM.mem_io_deg4_gates 3 := by
  decide


#print axioms b12_s2_self_justifying
#print axioms b12_s2_stored_Rprog_domain_empty
#print axioms b12_s1_empty_tables_accept_arbitrary_self_io
#print axioms b12_s1_alpha_beta_phantom
#print axioms b12_s3_empty_row_countermodel
#print axioms b12_s4_empty_compute_accepted
#print axioms b12_s4_accepted_not_in_readout
#print axioms b12_s4_declares_one_memory_root
#print axioms b12_s5_unrelated_model
#print axioms b12_s5_unrelated_model_verifies
#print axioms b12_s6_problem_is_compute_only
#print axioms b12_s6_accepted_is_compute_only
#print axioms b12_s7_tag_parameters_phantom
#print axioms b12_asymptotic_family_fails_compute_hchar
#print axioms b12_s8_reject_vm_costed
#print axioms b12_thm54_final_cost_figures
#print axioms b12_paperNockCost_is_not_thm54_final

end Nock.RedTeam
