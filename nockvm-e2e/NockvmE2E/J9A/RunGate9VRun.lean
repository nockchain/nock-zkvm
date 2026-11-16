/-
**`verdict9V_run`**, the online twin of `verdict9_run` (J9A/E2EJ9ARun.lean).
From `verdict9V XI root H Hf FS FSf z π πF = .ok c` it produces every instance-side fact `exec_e2e_J9AV` needs:
the five `famGates` conjuncts (`hsh hshX hchips hmask hnumeralOk`), `XI.l = 170`, the witness `Wit9 (XI170 XI) c _`
(the datum `d` with `DatumOK9A`, `Link9`, `StmtP9A`, `InpLink9`, small ids, `hnum0`, the four layout conditions, no jet table,
the table restriction `R` with `hT hσ hfree`, `d.c = c`), and `setupGates (XI170 XI) = true` (`hgates` of the side chain).
-/
import NockvmE2E.J9A.RunGate9V
import NockvmE2E.J9A.E2EJ9ARun
set_option autoImplicit false
namespace NockvmE2E.J9A.RunGate9VRun
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.E2EJ9AToyR NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9V NockvmE2E.J9A.LagrJ9A
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- **the online verdict gives the instance-side hypotheses of `exec_e2e_J9AV`** (at `XI170 XI`) -/
theorem verdict9V_run {XI : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9V XI root H Hf FS FSf z π πF = .ok c) :
    shapeOkF famJ9A (XI170 XI) = true ∧ shapeXOkF famJ9A (XI170 XI) = true ∧ chipsOkF famJ9A (XI170 XI) = true ∧
    maskOkF famJ9A (XI170 XI) = true ∧ numeralOkF famJ9A (XI170 XI) = true ∧ XI.l = 170 ∧
    Wit9 (XI170 XI) c (fun _ => True) ∧ setupGates (XI170 XI) = true := by
  obtain ⟨hG, hl, hg, hs, -⟩ := verdict9V_sound h
  have hx := xi170_of_l hl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := NockvmE2E.J9A.E2EJ9ARun.run_hyps9 XI c (by rw [hx]; exact hG) hl (by rw [hx]; exact hg)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by rw [hx]; exact hs⟩

end NockvmE2E.J9A.RunGate9VRun

#print axioms NockvmE2E.J9A.RunGate9VRun.verdict9V_run
