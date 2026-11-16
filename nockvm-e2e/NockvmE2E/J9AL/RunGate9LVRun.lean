/-
**`verdict9LV_run`**, the J-9 AL twin of `verdict9V_run` (`J9A/RunGate9VRun.lean`).  From
`verdict9LV XI root H Hf FS FSf z π πF = .ok c` it produces the six `famGatesL` conjuncts (`hsh hshX hchips hmask hnumeralOk hpreg`), `XI.l = 170`, the witness
`Wit9L (XI170 XI) c _` (which carries `PrimsCan`, `PreLLink`, `hpL`, ...), and `setupGates (XI170 XI) = true`.  `hrt` (`primsRoundTrip`) is a conjunct of
`PrimsLink`, which `linkGate9L` checks; `PrimsCan` comes from `inpCanOkL`.  Not zero-knowledge.
-/
import NockvmE2E.J9AL.WitJ9AL

set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.RunGate9LVRun

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9L
open NockvmE2E.J9AL.WitJ9AL NockvmE2E.J9A.LagrJ9A
open NockvmE2E.J9AL.RVUJ9AL (PrimsCan)
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- the five canonicity fields of every prim record, from `inpCanOkL` -/
theorem primsCan_of_inpCanOkL {inp : PE.PubIn} (h : inpCanOkL inp = true) : PrimsCan inp := by
  unfold inpCanOkL at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro q hq
  have := h.2 q hq
  simp only [Bool.and_eq_true, NockvmE2E.Exec.VF.based, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩

/-- **`linkGate9L_wit`**: the runtime link gate (with the shape, `pregOkF` and `inpCanOkL`) gives the datum-side witness -/
theorem linkGate9L_wit (XI : ExecInst) (c : P8PublicClaim) (h : shapeOkF famJ9AL XI = true) (hpreg : pregOkF XI = true)
    (hcan : inpCanOkL XI.pubIn = true) (hg : linkGate9L XI c = true) : Wit9L XI c (fun _ => True) :=
  witness9L XI c h hpreg (primsCan_of_inpCanOkL hcan) (of_decide_eq_true hg) _ (fun _ => trivial)

/-- **the runtime gates give the instance-side hypotheses of `exec_e2e_J9AL`** (at `XI := XI170 XI0`) -/
theorem run_hyps9L (XI0 : ExecInst) (c : P8PublicClaim) (hG : famGatesL famJ9AL (XI170 XI0) = true) (hl : XI0.l = 170)
    (hcan : inpCanOkL (XI170 XI0).pubIn = true) (hg : linkGate9L (XI170 XI0) c = true) :
    shapeOkF famJ9AL (XI170 XI0) = true ∧ shapeXOkF famJ9AL (XI170 XI0) = true ∧ chipsOkF famJ9AL (XI170 XI0) = true ∧
    maskOkFL famJ9AL (XI170 XI0) = true ∧ numeralOkF famJ9AL (XI170 XI0) = true ∧ pregOkF (XI170 XI0) = true ∧ XI0.l = 170 ∧
    Wit9L (XI170 XI0) c (fun _ => True) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := famGatesL_sound hG
  exact ⟨h1, h2, h3, h4, h5, h6, hl, linkGate9L_wit _ c h1 h6 hcan hg⟩

/-- **the online verdict gives the instance-side hypotheses of `exec_e2e_J9ALV`** (at `XI170 XI`) -/
theorem verdict9LV_run {XI : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LV XI root H Hf FS FSf z π πF = .ok c) :
    shapeOkF famJ9AL (XI170 XI) = true ∧ shapeXOkF famJ9AL (XI170 XI) = true ∧ chipsOkF famJ9AL (XI170 XI) = true ∧
    maskOkFL famJ9AL (XI170 XI) = true ∧ numeralOkF famJ9AL (XI170 XI) = true ∧ pregOkF (XI170 XI) = true ∧ XI.l = 170 ∧
    Wit9L (XI170 XI) c (fun _ => True) ∧ setupGates (XI170 XI) = true := by
  obtain ⟨hG, hl, hcan, hg, hs, -⟩ := verdict9LV_sound h
  have hx := xi170_of_l hl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := run_hyps9L XI c (by rw [hx]; exact hG) hl (by rw [hx]; exact hcan) (by rw [hx]; exact hg)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by rw [hx]; exact hs⟩

end NockvmE2E.J9AL.RunGate9LVRun

#print axioms NockvmE2E.J9AL.RunGate9LVRun.primsCan_of_inpCanOkL
#print axioms NockvmE2E.J9AL.RunGate9LVRun.linkGate9L_wit
#print axioms NockvmE2E.J9AL.RunGate9LVRun.run_hyps9L
#print axioms NockvmE2E.J9AL.RunGate9LVRun.verdict9LV_run
