/-
  Nock/RedTeam/Batch1961Thm54Z1aChip.lean

  * slot-1 act `s0·(1 − z1)` and slot-2 act `s9·(1 − z1)` in `slot1Q` / `slot2Q` (and their RHS sums),
    the tower-local path slots `accSlotsPT` / `accSlotsPImT` (the shared `accSlotsP` untouched);
    `actPQ = s·(1 − z1)`, `actXQ` unchanged.
  * new gates `z1Gates` (38): `z1·(z1 − 1)`, `z1·(ax − 1)`, and over `𝕂′` (6 coordinates per fingerprint
    entry) `z1·s0·(e − s)` and `z1·s9·(sf2_f − sf1_e)` — the OP9 fields are `op9PathRec`'s root `sf1_e` /
    child `sf2_f` (`V_comp`'s OP9 record, `mem_root_3 = sf1_e`, `mem_child_3 = sf2_f`).
  * degrees: `qdeg_slots` restated (act degree 2, margin 0), `accGatesT_degree` restated
    (`accGates_degree2`), `z1Gates_degree ≤ 3`; chip tuple `(e, w, s, d, k) = (3, 410, 608, 4, 2)`.
  * Both VCL instances now supply the
    frame field's disjunction themselves.
-/
import Nock.RedTeam.Batch1960Thm54Z1aFrameAxis1
import Nock.RedTeam.Batch1956Thm54VclCompletenessToy
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1961

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.Reified Module Nock.NockVMROM.Thm54.StrictExtension

section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- **The chip tuple** `(3, 410, 608, 4, 2)`. -/
theorem chip_tuple {h n e : ℕ} (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).w = 410 ∧
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).s = 608 ∧
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).d = 4 :=
  ⟨vclRAPQ7T_w b δ chalV pubVal orbit H, vclRAPQ7T_s b δ chalV pubVal orbit H,
    (vclRAPQ7T_d b δ chalV pubVal orbit H).1⟩

/-- Every gate, `z1` included, has degree `≤ 4`; the `z1` gates `≤ 3`. -/
theorem degrees (n e : ℕ) :
    (∀ g ∈ vclGatesQ7T n e b δ, g.degree ≤ 4) ∧ (∀ g ∈ z1Gates b δ, g.degree ≤ 3) ∧
      qdeg F (slot1Q F δ) ≤ 4 ∧ qdeg F (slot2Q F δ) ≤ 4 :=
  ⟨vclGatesQ7T_degree n e b δ, z1Gates_degree b δ, (qdeg_slots F δ).2.1, (qdeg_slots F δ).2.2⟩

/-- **NC (a): a `z1 = 1` OP0 row whose result fingerprint differs from its subject's is rejected**
(entry `0`: `e.size ≠ s.size` over `𝕂′`). -/
theorem nc_z1_e_ne_s [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (env : Env F) (hz : env.trace z1Col = 1) (h0 : env.trace 0 = 1)
    (hne : Q.val δ (entryQ F (op0PathRec ⟨3, by decide⟩)) (gatherEnv b env) env ≠
      Q.val δ (entryQ F (op0PathRec ⟨0, by decide⟩)) (gatherEnv b env) env) :
    ¬ ∀ g ∈ z1Gates b δ, g.eval env = 0 := by
  intro h
  apply hne
  exact z1Eq_entry δ b env 0 op0PathRec 0
    (fun g hg => h g (by simp only [z1Gates, List.mem_append]
                         exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨0, List.mem_finRange 0, hg⟩)))) hz h0

/-- **NC (a′), the control**: the SAME row with `z1 = 0` passes every `z1` gate (so (a) is the
`z1` identity gate at work, not an unrelated gate). -/
theorem nc_z1_zero_passes (env : Env F) (hz : env.trace z1Col = 0) : ∀ g ∈ z1Gates b δ, g.eval env = 0 :=
  z1Gates_of_zero δ b env hz

/-- **NC (b): a `z1 = 1` row whose axis is not `1` is rejected** (`z1·(ax − 1)`). -/
theorem nc_z1_ax_ne_one (env : Env F) (hz : env.trace z1Col = 1) (hax : env.trace axCol ≠ 1) :
    ¬ ∀ g ∈ z1Gates b δ, g.eval env = 0 := by
  intro h
  have h1 := h z1AxGate (by simp [z1Gates])
  simp only [z1AxGate, CoordinateCompiler.CoeffExpr.eval, hz, one_mul] at h1
  exact hax (sub_eq_zero.mp h1)

/-- **A `z1` row makes no path request**: the path activity `s0·(1 − z1)` is `0` at `z1 = 1`. -/
theorem z1_no_path_request (env : Env F) (hz : env.trace z1Col = 1) :
    actPQ (K := K) δ env 0 = 0 ∧ actPQ (K := K) δ env 1 = 0 := by
  simp [actPQ, hz]

end

/- **NC (c), reused**: before the `z1` column the honest pipeline cannot serve `[0 1]`: the axis-1
read violates `hax1` (`Batch1956.nc_hax1_axis1`, printed below; the path chip cannot provide axis 1,
SHD `shd_axis1_first`). -/

end Nock.RedTeam.Batch1961

#print axioms Nock.RedTeam.Batch1956.nc_hax1_axis1
#print axioms Nock.RedTeam.Batch1961.chip_tuple
#print axioms Nock.RedTeam.Batch1961.degrees
#print axioms Nock.RedTeam.Batch1961.nc_z1_e_ne_s
#print axioms Nock.RedTeam.Batch1961.nc_z1_zero_passes
#print axioms Nock.RedTeam.Batch1961.nc_z1_ax_ne_one
#print axioms Nock.RedTeam.Batch1961.z1_no_path_request
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerP_act_or_ident
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.node_records_CFT
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.compSoundnessVCLT
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7.node_records_Q7G
