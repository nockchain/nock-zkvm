/-
  Nock/RedTeam/Batch605Thm54PreseedStopReceipt.lean

  Result: on EVERY `Vcomp`-valid row in state `s1` (OP1), the result `e` equals `mr1.child`, the
  memory-served tail of the formula. So an OP1 "literal" row has no compute-side leaf of its
  own: its result is whatever noun the memory forest serves as the formula's tail, cell or atom.

  Identity; checked read-only against the target's build.
-/
import Nock.ComputeTable
import Nock.RedTeam.Batch600Thm54PreseedAtomDomainStop

set_option autoImplicit false

namespace Nock.RedTeam.Batch605

open Nock.ComputeTable

variable {K : Type*} [Field K]

/-- Check 1 (structural): every `Vcomp`-valid OP1 row's result is the memory-served formula tail. -/
theorem op1_result_is_mr1_child (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s1) :
    pub.e = pub.mr1.child := by
  obtain ⟨_, hmr1, _, _, heval⟩ := hv
  have he : pub.e = dec.f_t := by
    unfold evalV at heval
    rw [hs] at heval
    exact heval.1
  rw [he, hmr1]

theorem op1_gate_is_on_served_child (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s1) :
    pub.e.leaf = pub.mr1.child.leaf := by
  rw [op1_result_is_mr1_child inp pub dec hv hs]

theorem batch600_row_served_child_is_cell (z alpha a : K) :
    (Batch600.honestOp1Row z alpha a).mr1.child = Batch600.honestOp1Result z a := by
  have hv := Batch600.honest_op1_cell_row_valid z alpha a
  have := op1_result_is_mr1_child _ _ _ hv (Batch600.honest_op1_row_state z alpha a)
  rw [← this]
  rfl

/-- Re-stated: for a fixed fill `atom` and `b 0 = 1`,
the gate holds iff `z * a = atom - 1`; with `a ≠ 0` that is ONE seed. -/
theorem cell_row_gate_pins_seed {F : Type*} [Field F] [Algebra F K]
    (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1) (z a : K) (atom : F) :
    Batch600.AtomGates b (Batch600.honestOp1Result z a).leaf atom ↔
      1 + z * a = algebraMap F K atom := by
  rw [Batch600.atom_gates_iff, Batch600.honest_op1_result_leaf, hb]
  simp [Algebra.smul_def]

end Nock.RedTeam.Batch605

#print axioms Nock.RedTeam.Batch605.op1_result_is_mr1_child
#print axioms Nock.RedTeam.Batch605.batch600_row_served_child_is_cell
#print axioms Nock.RedTeam.Batch605.cell_row_gate_pins_seed
