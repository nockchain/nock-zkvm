/-
 `fixOps` in closed form (`fixOps_eq`): the openings of the flat side verifier are `(j, o, c * cs^(off j + o), vF[j][o])` in j-major order
(coefficient of the i-th opening = `pw cs one i`, right-multiplied powers).  Needed by the word0 link of conjunct 5.  `hglue_J8` is NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue4` is complete.
-/
import NockvmE2E.Exec.SideGlue3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SideGlue
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.SideInst

/-- right-multiplied powers `c * cs^i` -/
def pw (cs c : VF.K3) (i : ℕ) : VF.K3 := (fun a => VF.K3.mul a cs)^[i] c

theorem pw_succ (cs c : VF.K3) (i : ℕ) : pw cs c (i + 1) = VF.K3.mul (pw cs c i) cs := by
  unfold pw; rw [Function.iterate_succ_apply']

theorem pw_add (cs c : VF.K3) (i j : ℕ) : pw cs c (i + j) = pw cs (pw cs c j) i := by
  unfold pw; rw [Function.iterate_add_apply]

theorem inner_fold (j : ℕ) (cs : VF.K3) (v : ℕ → VF.K3) (m : ℕ) : ∀ (arr : Array (ℕ × ℕ × VF.K3 × VF.K3)) (c : VF.K3),
    (List.range m).foldl (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) o => (st.1.push (j, o, st.2, v o), VF.K3.mul st.2 cs)) (arr, c) =
      (arr ++ ((List.range m).map fun o => (j, o, pw cs c o, v o)).toArray, pw cs c m) := by
  induction m with
  | zero => intro arr c; simp [pw]
  | succ m ih =>
    intro arr c
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil, Prod.mk.injEq]
    refine ⟨?_, (pw_succ cs c m).symm⟩
    simp only [Array.push_eq_append, Array.append_assoc]
    congr 1
    simp

/-- the flat openings of `fixOps` in closed form (fold form) -/
theorem fixOps_fold (XI : ExecInst) (cols : Array FixCol) (cs : VF.K3) (vF : Array (Array VF.K3)) (n : ℕ) :
    (List.range n).foldl
      (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) j =>
        (List.range (fixLen XI cols[j]!)).foldl
          (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) o => (st.1.push (j, o, st.2, (vF[j]!)[o]!), VF.K3.mul st.2 cs)) st)
      (#[], VF.K3.one) =
    (((List.range n).flatMap fun j => (List.range (fixLen XI cols[j]!)).map fun o =>
        (j, o, pw cs VF.K3.one (((List.range j).map fun j' => fixLen XI cols[j']!).sum + o), (vF[j]!)[o]!)).toArray,
      pw cs VF.K3.one (((List.range n).map fun j' => fixLen XI cols[j']!).sum)) := by
  induction n with
  | zero => simp [pw]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [inner_fold]
    have e : ∀ o, pw cs (pw cs VF.K3.one (((List.range n).map fun j' => fixLen XI cols[j']!).sum)) o =
        pw cs VF.K3.one (((List.range n).map fun j' => fixLen XI cols[j']!).sum + o) := fun o => by
      rw [Nat.add_comm, pw_add]
    refine Prod.ext ?_ ?_
    · simp only [e, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_toArray]
    · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [e]

/-- **`fixOps_eq`**: the openings of the flat side verifier, closed form (`off j` = `offX`-style prefix sum of the column lengths) -/
theorem fixOps_eq (XI : ExecInst) (cols : Array FixCol) (cs : VF.K3) (vF : Array (Array VF.K3)) :
    fixOps XI cols cs vF =
      ((List.range cols.size).flatMap fun j => (List.range (fixLen XI cols[j]!)).map fun o =>
        (j, o, pw cs VF.K3.one (((List.range j).map fun j' => fixLen XI cols[j']!).sum + o), (vF[j]!)[o]!)).toArray := by
  unfold fixOps
  rw [fixOps_fold]

end NockvmE2E.Exec.SideGlue

#print axioms NockvmE2E.Exec.SideGlue.inner_fold
#print axioms NockvmE2E.Exec.SideGlue.fixOps_eq
