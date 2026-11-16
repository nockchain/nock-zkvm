/-
  NockvmE2E/Z38/RunGate9LJVRun.lean

  `verdict9LJV_run`: twin of `verdict9LV_run` (J9AL/RunGate9LVRun.lean).  From `verdict9LJV XI root H Hf FS FSf z π πF = .ok c` it produces the six `famGatesL`
  conjuncts, `XI.l = 170`, `Wit9LJ (XI170 XI) c _` and `setupGates (XI170 XI) = true`.  `jetPreOkF` is used inside the witness and not returned.
  Not zero-knowledge.
-/
import NockvmE2E.Z38.WitJ9ALJ
import NockvmE2E.J9AL.RunGate9LVRun

set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.RunGate9LJVRun

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9L
open NockvmE2E.Z38.RunGate9LJ NockvmE2E.Z38.IfaceJ NockvmE2E.Z38.WitJ9ALJ
open NockvmE2E.Z38.JetPre
open NockvmE2E.J9A.LagrJ9A (numeralOkF)
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- **the online verdict at the jet family gives the instance-side hypotheses of `exec_e2e_J9ALV`** (at `XI170 XI`) -/
theorem verdict9LJV_run {XI : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LJV XI root H Hf FS FSf z π πF = .ok c) :
    shapeOkF famJ9AL (XI170 XI) = true ∧ shapeXOkF famJ9AL (XI170 XI) = true ∧ chipsOkF famJ9AL (XI170 XI) = true ∧
    maskOkFL famJ9AL (XI170 XI) = true ∧ numeralOkF famJ9AL (XI170 XI) = true ∧ pregOkF (XI170 XI) = true ∧ XI.l = 170 ∧
    Wit9LJ (XI170 XI) c (fun _ => True) ∧ setupGates (XI170 XI) = true := by
  have hh := verdict9LJV_sound h
  obtain ⟨hG, hl, hcan, hg, hs, -⟩ := hh
  have hx := xi170_of_l hl
  rw [← hx] at hG hcan hg hs
  obtain ⟨hGL, hjp⟩ := famGatesLJ_sound hG
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := famGatesL_sound hGL
  exact ⟨h1, h2, h3, h4, h5, h6, hl, linkGate9LJ_wit _ c h1 h6 hjp hcan hg, hs⟩

end NockvmE2E.Z38.RunGate9LJVRun

#print axioms NockvmE2E.Z38.RunGate9LJVRun.verdict9LJV_run
