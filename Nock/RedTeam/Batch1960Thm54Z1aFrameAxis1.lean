/-
  Nock/RedTeam/Batch1960Thm54Z1aFrameAxis1.lean

  The (c-min) design serves OP0's axis-1 read and OP9's axis-1 arm by the compute row's own gates
  (the `z1` column, next batch), with no memory lookup.  The repair:

  * `SVJoinF.op0ResF` / `op9ArmF` : at `ax = 1` the subject / the core, else the oracle;
    `c2EvaluationF` / `c2JoinFuelF` read them (and `c2EvaluationF` takes `ax`, `subj`);
  * `SVInductionGenericF.c2RecF` : the field join's record function (`Batch1171.c2Rec`
    with OP0's child `op0ResF`), read by `RootGoodFJoin`;
  * `CompSoundnessFamily.node_records` gains the disjunct `((s0,1) ∨ (s9,2)) ∧ joinRecordAxis = 1 ∧
    trace child = trace root`; `StandaloneGeneric.recOK_row` takes it (`Noun.slot 1 = id`), and its
    served branch handles a served axis-1 record (`slot 1 rt = some ch` ⇒ `ch = rt = root`);
  * both VCL instances supply the served disjunct unchanged (`Or.inl`): z1 = 0 everywhere.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.VclL.Compute.KeysQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1960

open Nock Nock.ComputeTable Nock.MemoryTable Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVJoinF Nock.NockVMROM.Thm54.SVInductionGenericF
open Nock.NockVMROM.Thm54.SVFrame
open Nock.GlobalCarryRecognizer

/-! ## 1. NC: the old record function forces the oracle at axis 1 -/

theorem old_op0_record (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (subj f : Noun)
    (kids : List ComputeRowSkeleton) :
    Batch1171.c2Rec sv ax .s0 S subj f kids 1 = ⟨subj, sv .verify_child (S + 2), ax (S + 2)⟩ := rfl

/-- **Old record, axis 1: the oracle must BE the subject.** -/
theorem old_axis1_forces_oracle (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (subj f : Noun)
    (kids : List ComputeRowSkeleton) (hax : ax (S + 2) = 1)
    (hok : Noun.slot (Batch1171.c2Rec sv ax .s0 S subj f kids 1).axis
        (Batch1171.c2Rec sv ax .s0 S subj f kids 1).root =
      some (Batch1171.c2Rec sv ax .s0 S subj f kids 1).child) :
    sv .verify_child (S + 2) = subj := by
  rw [old_op0_record] at hok
  simp only [hax, Noun.slot, Option.some.injEq] at hok
  exact hok.symm

/-- **NC (discriminating)**: a subject-blind oracle breaks the old record at axis 1... -/
theorem nc_old_axis1_fails (kids : List ComputeRowSkeleton) :
    ¬ Noun.slot (Batch1171.c2Rec (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).axis
        (Batch1171.c2Rec (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).root =
      some (Batch1171.c2Rec (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).child := by
  rw [old_op0_record]; simp [Noun.slot]

/-- ... and the REPAIRED record satisfies the slot at axis 1 for EVERY oracle. -/
theorem new_axis1_slot (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (subj f : Noun)
    (kids : List ComputeRowSkeleton) (hax : ax (S + 2) = 1) :
    Noun.slot (c2RecF sv ax .s0 S subj f kids 1).axis (c2RecF sv ax .s0 S subj f kids 1).root =
      some (c2RecF sv ax .s0 S subj f kids 1).child := by
  rw [c2RecF_s0_1, op0ResF_of_eq subj hax]; simp [hax, Noun.slot]

/-- The NC instance under the repaired record (same oracle, same subject): accepted. -/
theorem new_axis1_instance (kids : List ComputeRowSkeleton) :
    Noun.slot (c2RecF (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).axis
        (c2RecF (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).root =
      some (c2RecF (fun _ _ => .atom 0) (fun _ => 1) .s0 0 (.atom 1) (.atom 0) kids 1).child :=
  new_axis1_slot _ _ 0 _ _ kids rfl

/-- **Off axis 1 the join is unchanged**: OP0's result and OP9's arm are the served oracle. -/
theorem off_axis1_unchanged (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (subj core : Noun)
    (h2 : ax (S + 2) ≠ 1) (h3 : ax (S + 3) ≠ 1) :
    op0ResF sv ax S subj = sv .verify_child (S + 2) ∧ op9ArmF sv ax S core = sv .verify_child (S + 3) :=
  ⟨op0ResF_of_ne subj h2, op9ArmF_of_ne core h3⟩

/-! ## 2. -/

/-- **`RecOK` at an axis-1 OP0 row from fingerprints alone**: if the trace record's child equals its
root (`z1·s0·(e − s) = 0`), the join's OP0 record passes `RecOK`'s obligation — no noun-level
fingerprint injectivity, hence no new collision event. -/
theorem axis1_recOK {Kf : Type} [Field Kf] (z : Kf) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (row : (State × DTcomp Kf) × ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton)
    (hax : ax (row.2 + 2) = 1) (hcr : (traceRecOf row 1).child = (traceRecOf row 1).root)
    (henc : enc z (c2RecF sv ax .s0 row.2 subj f kids 1).root = (traceRecOf row 1).root) :
    Noun.slot (c2RecF sv ax .s0 row.2 subj f kids 1).axis (c2RecF sv ax .s0 row.2 subj f kids 1).root =
        some (c2RecF sv ax .s0 row.2 subj f kids 1).child ∧
      enc z (c2RecF sv ax .s0 row.2 subj f kids 1).child = (traceRecOf row 1).child := by
  refine ⟨new_axis1_slot sv ax row.2 subj f kids hax, ?_⟩
  rw [hcr, ← henc, c2RecF_s0_1, op0ResF_of_eq subj hax]

/-! ## 3. -/

section natLift
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.RecordCarrier
variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K (ringChar K)]

/-- **`(ax : 𝔽) = 1` gives the decoded axis `1`** — no atom bound on the axis: `natLift` of a
field `1` is `1` whenever the characteristic exceeds `1`. -/
theorem natLift_one_of_eq (x : F) (hx : x = 1) (hc : 1 < ringChar K) :
    natLift (algebraMap F K x) = 1 := by
  rw [hx, map_one, ← Nat.cast_one]
  exact natLift_natCast hc

/-- At the VCL axis oracle: the row's `axCol` equal to `1` in `𝔽` makes `axB0Q7 (2i+2) = 1`
(the `joinRecordAxis` OP0 reads), for every characteristic above `1`. -/
theorem axB0Q7_eq_one_of_col {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T]
    (V : VerifierData F K hC S) (b : B0Cols F T) (i : ℕ)
    (hcol : (b (b0ColT axCol (by decide) axCol_round0)).eval (rowNodeQ7 V i) = 1)
    (hc : 1 < ringChar K) :
    axB0Q7 V b (2 * i + 2) = 1 ∧ axB0Q7 V b (2 * i + 3) = 1 := by
  rw [axB0Q7_s0, axB0Q7_s9]
  unfold b0NatAt
  exact ⟨natLift_one_of_eq _ hcol hc, natLift_one_of_eq _ hcol hc⟩

end natLift

end Nock.RedTeam.Batch1960

#print axioms Nock.RedTeam.Batch1960.old_axis1_forces_oracle
#print axioms Nock.RedTeam.Batch1960.nc_old_axis1_fails
#print axioms Nock.RedTeam.Batch1960.new_axis1_slot
#print axioms Nock.RedTeam.Batch1960.new_axis1_instance
#print axioms Nock.RedTeam.Batch1960.off_axis1_unchanged
#print axioms Nock.RedTeam.Batch1960.axis1_recOK
#print axioms Nock.RedTeam.Batch1960.natLift_one_of_eq
#print axioms Nock.RedTeam.Batch1960.axB0Q7_eq_one_of_col
#print axioms Nock.NockVMROM.Thm54.SVFrame.recOK_row
#print axioms Nock.NockVMROM.Thm54.SVFrame.ctxW_of_accepts
