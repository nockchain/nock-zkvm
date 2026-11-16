/-
  Nock/RedTeam/Batch1945Thm54RowTerms.lean

  **The per-row record identities of the honest VCL tower compute trace.**

  * `hrowX_T` / `hrowP_T` (`TowerRowTerms.lean`): at every row `j < N` of the honest trace with the accumulators
    zeroed, the export term is `Σ (compress xReq)⁻¹` over `shallowSided (rowExportKeys (gRow t j))` and the path term
    is `Σ (compress pReq)⁻¹` over `(rowPathKeys …).filter isPathAx`.  `HonestVCLT.hacc` is rebuilt
    on them (`TowerAccHonest.lean`).
  * Route: `gen_rowShape` (`TowerRowShape.lean`: by fuel induction over the emission arms, the per-state request keys
    are the formula tail / tail-tail at axis 2, `(subject, honestAx)` at `s0`, `(core, honestAx)` at `s9`; the formula,
    tail and tail-tail roots are CELLS, so `selfCell` keeps every export key: no atom-rooted export key occurs);
    `role_pub` / `role_dec` (the role columns of the 309 row are the fingerprint coordinates, off the overlay roles);
    `entryQ_role_val` (a role entry reads the row's role value); `rec0_vec`, `export10_compress`, `path_vec`
    (the slot records are `xReq` / `pReq`: slot 0 at side 1, slots 1/2 at side 0 with the trailing `0` entry);
    `row_inv` (honest inverses `den⁻¹`), `termQ_X_val` / `termQ_P_val`; `rhsX_eq` / `rhsP_eq` (the key lists).
  * NC: a role fingerprint perturbed by `d ≠ 0` at any record entry changes the compressed denominator and hence the
    reciprocal term (`nc_role_perturbed`, `nc_role_perturbed_inv`): the identities discriminate.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestAccept
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowTerms
import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint
import Nock.RedTeam.Batch1744Thm54VclLIOFieldQuad
import Nock.RedTeam.Batch1881Thm54TowerRowFactsAt

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1945

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

section NC
variable {L : Type} [Field L]

/-- **NC**: a record entry perturbed by `d ≠ 0` (a wrong role fingerprint) changes the compressed denominator
(`γ ≠ 0`). -/
theorem nc_role_perturbed {m : ℕ} (γ ρ d : L) (hγ : γ ≠ 0) (hd : d ≠ 0) (v : Fin m → L) (i : Fin m) :
    FiniteIO.compress (m := m) ⟨γ, ρ⟩ (fun c => v c + (Pi.single i d : Fin m → L) c) ≠
      FiniteIO.compress (m := m) ⟨γ, ρ⟩ v := by
  intro h
  simp only [FiniteIO.compress, Walk.rlc, add_right_inj] at h
  have h2 : ∑ c : Fin m, γ ^ (c : ℕ) * (v c + (Pi.single i d : Fin m → L) c) =
      (∑ c : Fin m, γ ^ (c : ℕ) * v c) + γ ^ (i : ℕ) * d := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc; simp [Pi.single_apply, hc]
    · simp
  rw [h2] at h
  have : γ ^ (i : ℕ) * d = 0 := by linear_combination h
  exact (mul_ne_zero (pow_ne_zero _ hγ) hd) this

/-- **NC (the term)**: the reciprocal terms of the perturbed and the honest record differ. -/
theorem nc_role_perturbed_inv {m : ℕ} (γ ρ d : L) (hγ : γ ≠ 0) (hd : d ≠ 0) (v : Fin m → L) (i : Fin m) :
    (FiniteIO.compress (m := m) ⟨γ, ρ⟩ (fun c => v c + (Pi.single i d : Fin m → L) c))⁻¹ ≠
      (FiniteIO.compress (m := m) ⟨γ, ρ⟩ v)⁻¹ := by
  intro h
  exact nc_role_perturbed γ ρ d hγ hd v i (inv_injective h)

end NC

end Nock.RedTeam.Batch1945

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.gen_rowShape
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.role_pub
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.role_dec
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.entryQ_role_val
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rec0_vec
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.export10_compress
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.path_vec
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.row_inv
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rhsX_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rhsP_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowX_row
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowP_row
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowX_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowP_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLT.hacc
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accepted_T
#print axioms Nock.RedTeam.Batch1945.nc_role_perturbed
#print axioms Nock.RedTeam.Batch1945.nc_role_perturbed_inv
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness_goldilocks
