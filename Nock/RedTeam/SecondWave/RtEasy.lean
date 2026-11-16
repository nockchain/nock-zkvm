import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Asymptotic

/-! Degeneracy witnesses for the cost-model, parametric cost-model, IO-bound, S6 and one-hot clauses of the Nock VM-ROM capstone. Each shows that a clause holds for a model with nonsense values in fields it never reads. -/

namespace RTNew

open Nock Nock.Framework Nock.NockVMROM

/-! ## N2 — `HasCostModel` never mentions `compCols`/`memCols` -/

/-- The reified cost with absurd column counts. -/
def absurdCost : CostModel :=
  { reifiedNockCost with compCols := 0, memCols := 999999 }

/-- The real Nock tag satisfies `HasCostModel` for a cost record whose column figures are nonsense. -/
@[reducible] def n2_absurd_columns_costed (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasCostModel (Tag F K α β Ksz) absurdCost where
  compMaxDegree_eq_four := rfl
  memMaxDegree_eq_four := rfl
  memory_fewer_constraints := by decide
  memory_fewer_deg4 := by decide

/-- Columns are a *phantom pair* of `HasCostModel`: the class transfers across any change of
    `compCols`/`memCols`. -/
theorem n2_columns_phantom (ι : Type) [VMSystem ι] (c : CostModel) (a b : ℕ) :
    HasCostModel ι c ↔ HasCostModel ι { c with compCols := a, memCols := b } :=
  ⟨fun h => ⟨h.compMaxDegree_eq_four, h.memMaxDegree_eq_four, h.memory_fewer_constraints,
      h.memory_fewer_deg4⟩,
   fun h => ⟨h.compMaxDegree_eq_four, h.memMaxDegree_eq_four, h.memory_fewer_constraints,
      h.memory_fewer_deg4⟩⟩

/-! ## N3 — `HasParamCostModel` never mentions the deployed `+IO` layer -/

/-- The reified parametric cost with every `+IO` field replaced by garbage. -/
def absurdParamCost : ParamCostModel :=
  { reifiedNockParamCost with
      compIOCols := ⟨0, 0⟩, compIODeg4 := ⟨0, 0⟩,
      memIOCols := ⟨777, 777⟩, memIODeg4 := ⟨777, 777⟩,
      compCols := ⟨0, 0⟩, memCols := ⟨0, 0⟩ }

/-- The Nock tag satisfies the parametric class with a model whose `+IO` layer — the actual
    Theorem-5.4 cost claim — is garbage, and
    whose base column counts are zero. -/
@[reducible] def n3_absurd_IO_param_costed
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasParamCostModel (Tag F K α β Ksz) absurdParamCost where
  compMaxDeg_le := by decide
  memMaxDeg_le := by decide
  mem_deg4_lt_comp := by intro e _; show 0 * e + 2 < 0 * e + 13; omega

/-- Six of the ten `ParamCostModel` fields — both column fields and the whole `+IO` block —
    are phantoms of `HasParamCostModel`. -/
theorem n3_io_layer_phantom (ι : Type) [VMSystem ι] (p : ParamCostModel)
    (q1 q2 q3 q4 q5 q6 : AffineE) :
    HasParamCostModel ι p ↔
      HasParamCostModel ι { p with compCols := q1, memCols := q2, compIOCols := q3, compIODeg4 := q4, memIOCols := q5, memIODeg4 := q6 } :=
  ⟨fun h => ⟨h.compMaxDeg_le, h.memMaxDeg_le, h.mem_deg4_lt_comp⟩,
   fun h => ⟨h.compMaxDeg_le, h.memMaxDeg_le, h.mem_deg4_lt_comp⟩⟩

/-! ## N4 — `TwoRAPVerificationModel.ioBound` is a phantom field -/

/-- The recorded `L_mIO^{M,K}` bound is never consumed by `HasTwoRAPVerification`: the class
    transfers across an arbitrary change of `ioBound`. -/
theorem n4_ioBound_phantom (ι : Type) [VMSystem ι] (M : MEF) (F : Type) [CommRing F]
    (m : TwoRAPVerificationModel ι M F) (n : ℕ) :
    HasTwoRAPVerification ι M F m ↔
      HasTwoRAPVerification ι M F { m with ioBound := n } :=
  ⟨fun h => ⟨h.compute_sound, h.memory_sound, h.shared_io⟩,
   fun h => ⟨h.compute_sound, h.memory_sound, h.shared_io⟩⟩

/-- Concretely: the shipped Nock S5 model with its IO bound zeroed still verifies, even though
    its `rapIOAccepts` is `L_mIO` at `Ksz`. -/
@[reducible] noncomputable def n4_nock_model_zero_ioBound
    (F K : Type) [Field F] [Field K] [Fintype K] [DecidableEq K] (α β : K) {Ksz : ℕ}
    (hK : 1 ≤ Ksz) :
    HasTwoRAPVerification (Tag F K α β Ksz) (nmrMEF F K) K
      { nockTwoRAPModel F K α β Ksz with ioBound := 0 } :=
  (n4_ioBound_phantom _ _ _ _ 0).mp (nock_hasTwoRAPVerification F K α β hK)

/-! ## N7 — S6 is definitionally the forward half of S2 -/

/-- The bundle's S6 clause is not an independent obligation: on the shipped instances the
    completeness model's two predicates are *definitionally* S2's `progAccepts`/`progSatisfiable`,
    so `HasPerfectCompleteness` is exactly the `.mp` of `HasCanonicalRAP.compute_iff`. -/
theorem n7_s6_is_s2_forward (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ)
    (p : ComputeProblem K) :
    ((nockCompletenessModel F K α β Ksz).accepted p ↔
        (nock_hasCanonicalRAP F K α β Ksz).progAccepts p) ∧
      ((nockCompletenessModel F K α β Ksz).hasSatisfyingAssignment p ↔
        (nock_hasCanonicalRAP F K α β Ksz).progSatisfiable p) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ## N5 — `OpcodeMemoryOneHot` never mentions `ι`, `M`, or the S1 separation -/

/-- S3 content transports across *any* change of VM tag, memory family, and S1 separation:
    no field of `OpcodeMemoryOneHot` references them.  This refutes the bundle docstring's
    "S3 `OpcodeMemoryOneHot` (over the *stored* S1 separation `uniqueMES`)". -/
def n5_oneHot_transport {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂]
    {M₁ M₂ : MEF} {F : Type} [CommRing F] {NOP MOP : ℕ}
    [S₁ : UniqueMemoryExecutionSeparable ι₁ M₁] [S₂ : UniqueMemoryExecutionSeparable ι₂ M₂]
    (O : @OpcodeMemoryOneHot ι₁ _ M₁ F _ NOP MOP S₁) :
    @OpcodeMemoryOneHot ι₂ _ M₂ F _ NOP MOP S₂ where
  Row := O.Row
  numericSelector := O.numericSelector
  structuralSelector := O.structuralSelector
  recordCount := O.recordCount
  numeric_boolean := O.numeric_boolean
  structural_boolean := O.structural_boolean
  exactly_one_action_per_compute_row := O.exactly_one_action_per_compute_row
  record_arity_le := O.record_arity_le
  record_pos := O.record_pos

#print axioms n2_absurd_columns_costed
#print axioms n2_columns_phantom
#print axioms n3_absurd_IO_param_costed
#print axioms n3_io_layer_phantom
#print axioms n4_ioBound_phantom
#print axioms n4_nock_model_zero_ioBound
#print axioms n7_s6_is_s2_forward
#print axioms n5_oneHot_transport

end RTNew
