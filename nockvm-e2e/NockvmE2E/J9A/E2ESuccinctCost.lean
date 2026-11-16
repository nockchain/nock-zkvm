/-
The cost clause: the verifier that accepted is succinct in the cost model.
`verdict9V_cost_hyps` derives the hypotheses of the generic `verifyOnline_cost` from `verdict9V … = .ok c`;
`verdict9V_cost` instantiates it at `vkOfRoot XI0 root`; `nock_e2e_J9A_succinct_SC` pairs clause (S) with clause (C).
definitions and theorems are untouched.

Scope: preprocessing verifier (honest VK); chip files trusted; `k ≥ 1`; jet-free instances only (T5: jet instances are
rejected on j9a); compiler TCB (the exe's `verdict9V` result is trusted from the Lean compiler/runtime); not ZK; RO model; non-adaptive.
Cost is a MODEL (`costModel`), linked to the program by inspection except goRootT (VerifyOnlineCost header); `pubCheck9` (claim-size)
is not costed; verify-time instance work of `verdict9V` (gates, setup) is not in the cost (preprocessing verifier; the
online-only path is `verdict9VO`).
-/
import NockvmE2E.J9A.E2ESuccinct
import NockvmE2E.Exec.VerifyOnlineCost
import NockvmE2E.Exec.SideGlue18
import NockvmE2E.Exec.SoundOnlineP
set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.maxSteps 2000
namespace NockvmE2E.J9A.E2ESuccinctCost
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VF NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9V NockvmE2E.Exec.ShapeF
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- the hypotheses of `verifyOnline_cost`, from an accepting `verdict9V` run -/
theorem verdict9V_cost_hyps {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof}
    {πF : FixProof} {c : P8PublicClaim} (hv : verdict9V XI0 root H Hf FS FSf z π πF = .ok c) :
    π.pos.size = (vkOfRoot XI0 root).X.l ∧ πF.pos.size = (vkOfRoot XI0 root).X.l ∧
      1 ≤ (vkOfRoot XI0 root).X.nD ∧ (vkOfRoot XI0 root).X.hN ≤ 2 ^ (vkOfRoot XI0 root).X.nD := by
  obtain ⟨hfam, -, -, -, hon⟩ := verdict9V_sound hv
  have hsh := (NockvmE2E.Exec.FamGates.famGates_sound hfam).1
  have hN : XI0.hN = 2 ^ (XI0.k + 1) := hN_of_shapeF hsh
  have hD : XI0.nD = XI0.k + 7 := by
    have := hsh
    unfold shapeOkF at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    tauto
  have hok : verifyOnlineE' (vkOfRoot XI0 root) H Hf FS FSf z π πF = .ok () := by
    unfold verifyOnline' at hon
    split at hon
    · rename_i u hu; cases u; exact hu
    · cases hon
  obtain ⟨-, -, h3, -, -, -, -, hfix, -⟩ := (verifyOnlineE'_ok_iff _ _ _ _ _ _ _ _).1 hok
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  have h4 : πF.pos.size = (vkOfRoot XI0 root).X.l := by
    -- same extraction as `SideGlue18.verifyFix'_sizes` (not importable: it needs the section's `SampleableType` instance)
    unfold verifyFix' at hfix
    simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at hfix
    obtain ⟨h1, h2, _⟩ := hfix
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1 h2
    exact h1.1.1.1.2
  refine ⟨h3.2, h4, ?_, ?_⟩
  · show 1 ≤ XI0.nD; omega
  · show XI0.hN ≤ 2 ^ XI0.nD
    rw [hN, hD]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- the full conclusion of `verifyOnline_cost` at the accepted VK -/
theorem verdict9V_cost {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof}
    {πF : FixProof} {c : P8PublicClaim} (hv : verdict9V XI0 root H Hf FS FSf z π πF = .ok c) (zeta cs : VF.K3) :
    type_of% (verifyOnline_cost (vkOfRoot XI0 root) H z π πF zeta cs (verdict9V_cost_hyps hv).1 (verdict9V_cost_hyps hv).2.1
      (verdict9V_cost_hyps hv).2.2.1 (verdict9V_cost_hyps hv).2.2.2) :=
  verifyOnline_cost (vkOfRoot XI0 root) H z π πF zeta cs (verdict9V_cost_hyps hv).1 (verdict9V_cost_hyps hv).2.1
    (verdict9V_cost_hyps hv).2.2.1 (verdict9V_cost_hyps hv).2.2.2

set_option maxHeartbeats 4000000 in
/-- **`nock_e2e_J9A_succinct_SC`**: clause (S) (`nock_e2e_J9A_succinct`, its statement verbatim via `type_of%`) together with clause (C):
the cost model of the accepted run at `vkOfRoot XI0 root` is `≤ 6000·S⁶`. -/
theorem nock_e2e_J9A_succinct_SC (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z0 : List ℕ) (π0 : FlatProof)
    (πF0 : FixProof) (c : P8PublicClaim)
    (hv : NockvmE2E.J9A.RunGate9V.verdict9V XI0 root H Hf FS FSf z0 π0 πF0 = .ok c) :
    type_of% (NockvmE2E.J9A.E2ESuccinct.nock_e2e_J9A_succinct XI0 root H Hf FS FSf z0 π0 πF0 c hv) ∧
      costModel (Dims.ofRun (vkOfRoot XI0 root) z0 π0 πF0) ≤ 6000 * (Dims.ofRun (vkOfRoot XI0 root) z0 π0 πF0).S ^ 6 :=
  ⟨NockvmE2E.J9A.E2ESuccinct.nock_e2e_J9A_succinct XI0 root H Hf FS FSf z0 π0 πF0 c hv,
   (verdict9V_cost (XI0 := XI0) (root := root) (H := H) (Hf := Hf) (FS := FS) (FSf := FSf) (z := z0) (π := π0) (πF := πF0)
     (c := c) hv VF.K3.zero VF.K3.zero).2.2.2.2.2.2.2.2⟩

#print axioms verdict9V_cost_hyps
#print axioms verdict9V_cost
#print axioms nock_e2e_J9A_succinct_SC

end NockvmE2E.J9A.E2ESuccinctCost
