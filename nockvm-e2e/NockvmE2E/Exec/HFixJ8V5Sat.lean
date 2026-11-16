/-
 non-vacuity of the instance hypotheses of `hglue_J8` / `exec_e2e_J8V5` at the literal J-8 toy instance `toy1X`
(accept-vacuity rule): `hsh` [kernel], `hdomS` [kernel], `hl` [kernel] and `hz` [kernel] hold jointly; `hgates` is [executed] only (not kernel-evaluated: OOM); `hk : 1 ≤ k` does NOT (toy1X has k = 0).

LABEL: `hk` fails at toy1X (k = 0) [kernel, `toy1X_k0`]; `hk` holds jointly with the gates at ne5 (k=2) / add (k=6) / mat (k=8) [executed: J-8 exe ACCEPT; NOT kernel literals -- no ne5/add/mat ExecInst literal exists in NockvmE2E].  `hk` is not weakened.  `hz` is witnessed at `Statement = Salt = Unit`.
-/
import NockvmE2E.Exec.E2EJ8ToyD
import NockvmE2E.Exec.SideGlue20

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.HFixJ8V5Sat
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.J8Shape NockvmE2E.Exec.Toy1X
open NockvmE2E.Exec.E2EMain (XI170)

/-- the shape check holds at `XI170 toy1X` (`E2EJ8ToyD.hsh`) and `l = 170` -/
theorem toy1X_l : toy1X.l = 170 := by decide +kernel

-- `setupGates (XI170 toy1X) = true`: NOT kernel-evaluated here (`decide +kernel` on the full toy1X instance exceeded the 20G scope, job 28822);
-- label [executed]: the prover's `setup'` returns `some` on toy1/ne5/add/mat (the J-8 exe ACCEPTs them), and `setup'_some` (HFixFri.lean) gives
-- `setup' X Hf = some vk → setupGates X = true`; no kernel literal fact `setupGates (XI170 toy1X) = true` exists in the tree.

/-- NOT satisfiable at `toy1X`: its FRI depth is `k = 0`, so the binder `hk : 1 ≤ k` (shared with `exec_e2e_J8V4`) fails there -/
theorem toy1X_k0 : (XI170 toy1X).k = 0 := by
  rw [E2EJ8ToyD.xi170]; decide +kernel

theorem toy1X_dom : 2 ^ (∑ _j : Fin ((XI170 toy1X).k + 1), ((1 : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ (XI170 toy1X).nD := by
  rw [E2EJ8ToyD.xi170]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, PNat.one_coe, Nat.mul_one, PNat.val_ofNat]
  decide +kernel

/-- **joint satisfiability** of the instance hypotheses of `hglue_J8` / `exec_e2e_J8V5` at the literal `toy1X` -/
theorem hglue_J8_hyps_sat :
    j8ShapeOk (XI170 toy1X) = true ∧
      2 ^ (∑ _j : Fin ((XI170 toy1X).k + 1), ((1 : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ (XI170 toy1X).nD ∧ toy1X.l = 170 ∧
      ∃ (encZ : Unit × Unit → List ℕ) (decZ : List ℕ → Unit × Unit), ∀ x, decZ (encZ x) = x :=
  ⟨E2EJ8ToyD.hsh, toy1X_dom, toy1X_l, fun _ => [], fun _ => ((), ()), fun _ => rfl⟩

end NockvmE2E.Exec.HFixJ8V5Sat

#print axioms NockvmE2E.Exec.HFixJ8V5Sat.hglue_J8_hyps_sat
#print axioms NockvmE2E.Exec.HFixJ8V5Sat.toy1X_k0
