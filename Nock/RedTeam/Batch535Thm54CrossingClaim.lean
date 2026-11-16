/-
  Nock/RedTeam/Batch535Thm54CrossingClaim.lean

  **Can the crossing become a false *program* claim?**

  Paper `V_comp` OP0: `mem_record_2 =
  (input_subject, evaluation, f_t.leaf, timestamp_2)`.  The compute
  chip pins the claimed evaluation to the record; it does not check
  `Noun.slot`.  So `*[S [0 2]]` then `*[result [0 2]]` emits
  `(S, claimed₁, 2, ts₁)` then `(claimed₁, claimed₂, 2, ts₂)`.

  A full hostile compute+memory interpolant at `nockCompiles_zmod` is
  not constructed.  The noun identity is compiled; the compute-side
  emission is the paper's OP0 record, not a chip trace.
-/
import Nock.Reference
import Nock.RedTeam.Batch534Thm54CrossingVmem

set_option autoImplicit false

namespace Nock.RedTeam.Batch535

open Nock
open Nock.RedTeam.Batch534

/-- The program `*[S [0 2]]` then `*[· [0 2]]` asks `/[2 /[2 S]]`.
    On `S = cons(cons(u,v), w)` that is `u`.  The crossing serves `w`. -/
theorem program_asks_u_crossing_serves_w (u v w : ℕ) (h : u ≠ w) :
    let R := Noun.cell (Noun.atom u) (Noun.atom v)
    let S := Noun.cell R (Noun.atom w)
    Noun.slot 2 S = some R ∧
      Noun.slot 2 R = some (Noun.atom u) ∧
      Noun.slot 3 S = some (Noun.atom w) ∧
      some (Noun.atom u) ≠ some (Noun.atom w) := by
  intro R S
  exact ⟨by simp [Noun.slot, R, S], slot2_is_head u v,
    slot3_is_tail u v w, (crossing_lookup_false u v w h).2⟩

/-- Paper `:1864-1867`: OP0's second record is
    `(input_subject, evaluation, formula_tail.leaf)`.  No `slot`
    conjunct.  Named so the end-to-end claim is not a chip theorem. -/
def op0_record_is_claimed_evaluation : String :=
  "V_comp OP0 mem_record_2 = (input_subject, evaluation, f_t.leaf, ts); no Noun.slot check (main.tex:1864-1867)"

theorem op0_does_not_check_slot :
    op0_record_is_claimed_evaluation =
      "V_comp OP0 mem_record_2 = (input_subject, evaluation, f_t.leaf, ts); no Noun.slot check (main.tex:1864-1867)" :=
  rfl

/-- A full hostile `nockCompiles_zmod` / joint-chip interpolant is
    not constructed.  Compute would emit the claimed OP0 record;
    nothing in `:1728-1742` objects to `(R, w, 2, ts)` as a *record*. -/
theorem end_to_end_interpolant_not_constructed :
    (Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  Nock.RedTeam.Batch534.chip_interpolant_not_constructed

end Nock.RedTeam.Batch535

#print axioms Nock.RedTeam.Batch535.program_asks_u_crossing_serves_w
#print axioms Nock.RedTeam.Batch535.op0_does_not_check_slot
