/-
  Nock/RedTeam/Batch758Thm54HbindComputeCancel.lean

  Notes only.  Brief Q2.

  `FP.cons z a b` is injective in `b` once `a.size ≠ 0` (`cons_right_cancel`).  An opcode row's
  formula head is the atom fingerprint `atomFP z op` (`Batch530.vcomp_f_h_eq_atomFP`, SVhead), whose
  size is `z ≠ 0`.  So on rows whose formula is `[op tail]` with `tail` bound only through the
  row's own `f` (OP0, OP1, OP3, OP4), `bindFP z tail f_t` follows from `bindFP z f`
  algebraically (`ht_of_opcode_head`): no memory record, no axis walk, no pair event.  OP0's `e` and OP9's arm are served
  record children: bound by (i) + (ii) alone when the skeleton reads them off the served row.
-/
import Nock.RedTeam.Batch525Thm54ComputeTreeBinds
import Nock.NockVMROM.Thm54.P8Core.Batch758Thm54HbindComputeCancel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch758

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.GlobalCarryRecognizer

variable {K : Type} [Field K] [DecidableEq K]

/-- **An opcode row's formula tail is bound by its formula alone**: if `f = cons(f_h, f_t)`,
`f_h = atomFP z op` and `f` binds `[op tail]`, then `f_t` binds `tail`. -/
theorem ht_of_opcode_head {z : K} (hz : z ≠ 0) (op : ℕ) (tail : Noun) {f f_h f_t : FP K}
    (hf : f = FP.cons z f_h f_t) (hh : f_h = FP.atomFP z (op : K))
    (hbind : bindFP z (Noun.cell (Noun.atom op) tail) f) :
    bindFP z tail f_t := by
  have h1 : FP.cons z (FP.atomFP z (op : K)) f_t =
      FP.cons z (FP.atomFP z (op : K)) (enc z tail) := by
    rw [← hh, ← hf, hbind, enc_cons hz, enc_atom, hh]
  exact cons_right_cancel (by simpa [FP.atomFP] using hz) h1

end Nock.RedTeam.Batch758

#print axioms Nock.RedTeam.Batch758.cons_right_cancel
#print axioms Nock.RedTeam.Batch758.ht_of_opcode_head
