/-
  Nock/RedTeam/Batch606Thm54PreseedComputeResults.lean

  Answer (compiled, per opcode, from `Vcomp` alone): no.
  - OP0: `e` is `mr2.child`'s root? — the record `mr2 = ⟨s, e, axis, ts⟩` carries `e` as the served
    child (memory-served);
  - OP1: `e = mr1.child`;
  - OP2, OP6, OP7, OP8: `e` is a sub-evaluation result (`sf3_e` / `sf2_e` / …) — derived;
  - OP3, OP5: `e` is the atom `?`/`=` of sub-results: `size = z`, `dyck = 0`, leaf `FP.qm`/`FP.eqOp` — forced;
  - OP4: `e = FP.inc z sf1_e` — forced from the sub-result;
  - cons: `e = FP.cons z sf1_e sf2_e` — forced;
  - OP9: `e = sf3_e`? — derived (`mr3` serves the core lookup).
  So the compute chip has no row on which a NEW atom leaf is free to be chosen; the free leaves of a
  trace live only in the memory forest's `halt` rows (and in the public claim). This is the premise
  that makes a memory-only pre-seed atom column (option 1) the right domain, and the compute gates of
  the authority's item 2 unnecessary. Identity; read-only against the target build.
-/
import Nock.ComputeTable

set_option autoImplicit false

namespace Nock.RedTeam.Batch606

open Nock.ComputeTable

variable {K : Type*} [Field K]

theorem evalV_of_vcomp (inp : Inputs K) (pub : Pub K) (dec : Dec K) (hv : Vcomp inp pub dec) :
    evalV inp pub dec := hv.2.2.2.2

/-- OP0: the record `mr2` serves the result as its child (`memBlk.s0`). -/
theorem op0_result_served (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s0) :
    pub.mr2.child = pub.e := by
  have hm := hv.2.2.2.1
  unfold memBlk at hm
  rw [hs] at hm
  rw [hm.1]

/-- OP3: the result is the atom `?[sf1_e]` — size `z`, dyck `0`, leaf `FP.qm z sf1_e` — determined. -/
theorem op3_result_determined (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s3) :
    pub.e.size = inp.z ∧ pub.e.dyck = 0 ∧ pub.e.leaf = FP.qm inp.z pub.sf1_e := by
  have he := evalV_of_vcomp inp pub dec hv
  unfold evalV at he
  rw [hs] at he
  exact ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩

/-- OP4: the result is the increment of the sub-result (`FP.inc`), fully determined. -/
theorem op4_result_determined (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s4) :
    pub.e = FP.inc inp.z pub.sf1_e := by
  have he := evalV_of_vcomp inp pub dec hv
  unfold evalV at he
  rw [hs] at he
  exact he.2.2.2.2.2.2

/-- OP5: the result is the atom `=[sf1_e sf2_e]` — size `z`, dyck `0`, leaf `FP.eqOp` — determined. -/
theorem op5_result_determined (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s5) :
    pub.e.size = inp.z ∧ pub.e.dyck = 0 ∧ pub.e.leaf = FP.eqOp pub.sf1_e pub.sf2_e := by
  have he := evalV_of_vcomp inp pub dec hv
  unfold evalV at he
  rw [hs] at he
  exact ⟨he.2.2.2.2.2.1, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2⟩

/-- cons: the result is `FP.cons z sf1_e sf2_e` — determined. -/
theorem cons_result_determined (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .cons) :
    pub.e = FP.cons inp.z pub.sf1_e pub.sf2_e := by
  have he := evalV_of_vcomp inp pub dec hv
  unfold evalV at he
  rw [hs] at he
  exact he.2.2.2.2.1

/-- OP6/OP7/OP8/OP9: the result is a sub-evaluation's result — derived. -/
theorem op6789_result_derived (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) :
    (pub.state = .s6 → pub.e = pub.sf1_e) ∧ (pub.state = .s7 → pub.e = pub.sf1_e) ∧
    (pub.state = .s8 → pub.e = pub.sf1_e) ∧ (pub.state = .s9 → pub.e = pub.sf2_e) := by
  have he := evalV_of_vcomp inp pub dec hv
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩ <;>
    (unfold evalV at he; rw [hs] at he)
  · exact he.2.2.1
  · exact he.2.2.1
  · exact he.2.2.1
  · exact he.2.2.2.1

/-- OP2: the result is the third sub-evaluation's result (derived). -/
theorem op2_result_derived (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s2) :
    pub.e = pub.sf3_e := by
  have he := evalV_of_vcomp inp pub dec hv
  unfold evalV at he
  rw [hs] at he
  exact he.2.2.2.2.2.2

end Nock.RedTeam.Batch606

#print axioms Nock.RedTeam.Batch606.op0_result_served
#print axioms Nock.RedTeam.Batch606.op3_result_determined
#print axioms Nock.RedTeam.Batch606.op4_result_determined
#print axioms Nock.RedTeam.Batch606.op5_result_determined
#print axioms Nock.RedTeam.Batch606.op2_result_derived
#print axioms Nock.RedTeam.Batch606.cons_result_determined
#print axioms Nock.RedTeam.Batch606.op6789_result_derived
