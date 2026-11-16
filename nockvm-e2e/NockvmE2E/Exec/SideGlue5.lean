/-
 conjunct-5 prerequisites: the index of opening `(j,o)` in `opList` is `offX j + o` (`opList_getElem`),
and `toKV (pw cs one i) = toKV cs ^ i` (`toKV_pw`).  Conjunct 5 and `hglue_J8` are NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue5` is complete.
-/
import NockvmE2E.Exec.SideGlue4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SideGlue
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.SideInst NockvmE2E.Exec.VL

/-- prefix sums are monotone -/
theorem sum_range_mono (m : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map m).sum ≤ ((List.range b).map m).sum := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem length_flatMap_range (m : ℕ → ℕ) (n : ℕ) :
    ((List.range n).flatMap fun j => (List.range (m j)).map (j, ·)).length = ((List.range n).map m).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.map_append, List.sum_append]
    simp

/-- general index lemma -/
theorem flatMap_range_getElem? (m : ℕ → ℕ) (n : ℕ) : ∀ j o, j < n → o < m j →
    ((List.range n).flatMap fun j => (List.range (m j)).map (j, ·))[((List.range j).map m).sum + o]? = some (j, o) := by
  induction n with
  | zero => intro j o hj; omega
  | succ n ih =>
    intro j o hj ho
    rw [List.range_succ, List.flatMap_append]
    by_cases hjn : j < n
    · have hlt : ((List.range j).map m).sum + o <
          ((List.range n).flatMap fun j => (List.range (m j)).map (j, ·)).length := by
        rw [length_flatMap_range]
        have := sum_range_mono m (show j + 1 ≤ n by omega)
        rw [List.range_succ, List.map_append, List.sum_append] at this
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at this
        omega
      rw [List.getElem?_append_left hlt]
      exact ih j o hjn ho
    · have hjn' : j = n := by omega
      subst hjn'
      rw [List.getElem?_append_right (by rw [length_flatMap_range]; omega), length_flatMap_range]
      simp [ho]

/-- the index of opening `(j,o)` in `opList` is `offX j + o` -/
theorem opList_getElem? (XI : ExecInst) (j o : ℕ) (hj : j < (fixCols XI).size) (ho : o < fixLen XI (fixCols XI)[j]!) :
    (opList XI)[offX XI j + o]? = some (j, o) := by
  unfold opList offX
  exact flatMap_range_getElem? (fun j => fixLen XI (fixCols XI)[j]!) _ j o hj ho

theorem opList_getElem (XI : ExecInst) (j o : ℕ) (hj : j < (fixCols XI).size) (ho : o < fixLen XI (fixCols XI)[j]!) :
    (opList XI)[offX XI j + o]! = (j, o) := by
  have h := opList_getElem? XI j o hj ho
  rw [getElem!_pos (opList XI) _ (by exact (List.getElem?_eq_some_iff.mp h).1)]
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h)

/-- `pw cs one i` as a power in `KC` -/
theorem toKV_pw_aux (cs : VF.K3) (c : VF.K3) (i : ℕ) : toKV (pw cs c i) = toKV c * toKV cs ^ i := by
  induction i with
  | zero => simp [pw]
  | succ i ih => rw [pw_succ, toKV_mul, ih, pow_succ]; ring

theorem toKV_pw (cs : VF.K3) (i : ℕ) : toKV (pw cs VF.K3.one i) = toKV cs ^ i := by
  rw [toKV_pw_aux, toKV_one, one_mul]

end NockvmE2E.Exec.SideGlue

#print axioms NockvmE2E.Exec.SideGlue.opList_getElem
#print axioms NockvmE2E.Exec.SideGlue.toKV_pw
