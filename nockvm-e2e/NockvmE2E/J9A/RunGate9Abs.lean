/-
INST-PARSE S7 (per-released-instance gate certificates), the ABSENT instance `abs9R`: `linkGate9` kernel-evaluated at the executed literal with its
claim `cAbs` (`gate_abs`), the decoder reading `cAbs` off its public input (`claimOf_abs`), `l = 170` (`abs9R_l`), and the negative
`gate_abs_wrongclaim` (the right instance with the false twin's claim `cAbsF` is rejected).  Separate module from `RunGate9` (which holds the toy
certificates) to keep each kernel job small.
-/
import NockvmE2E.J9A.RunGate9
set_option autoImplicit false
set_option maxRecDepth 100000
namespace NockvmE2E.J9A.RunGate9Abs
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.E2EJ9AToyR NockvmE2E.J9A.RunGate9
open Nock.NockVMROM.Thm54 (P8PublicClaim)

open Abs9R in
theorem abs9R_l : abs9R.l = 170 := by decide +kernel

open Abs9R in
theorem gate_abs : linkGate9 (XI170 abs9R) cAbs = true := by decide +kernel

open Abs9R in
/-- the gate binds the claim: the right instance with the false twin's claim is rejected -/
theorem gate_abs_wrongclaim : linkGate9 (XI170 abs9R) cAbsF = false := by decide +kernel

open Abs9R in
theorem claimOf_abs_fields : (claimOf abs9R.pubIn).map (fun c => (c.subject, c.formula, c.result)) =
    some (cAbs.subject, cAbs.formula, cAbs.result) := by decide +kernel

open Abs9R in
theorem claimOf_abs : claimOf abs9R.pubIn = some cAbs := by
  have h := claimOf_abs_fields
  rcases hc : claimOf abs9R.pubIn with _ | ⟨s, f, r⟩
  · rw [hc] at h; simp at h
  · rw [hc] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [cAbs] at h1 h2 h3 ⊢
    subst h1 h2 h3
    rfl

end NockvmE2E.J9A.RunGate9Abs

#print axioms NockvmE2E.J9A.RunGate9Abs.abs9R_l
#print axioms NockvmE2E.J9A.RunGate9Abs.gate_abs
#print axioms NockvmE2E.J9A.RunGate9Abs.gate_abs_wrongclaim
#print axioms NockvmE2E.J9A.RunGate9Abs.claimOf_abs
