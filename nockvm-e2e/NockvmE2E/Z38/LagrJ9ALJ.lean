/-
  NockvmE2E/Z38/LagrJ9ALJ.lean

  `hjet_of_PreJLink`: the closure at J-9 AL.  The `hjet` binder of `hLagr9L_of` (the J table's loaded fixed columns are the datum's) follows from
  `PreJLink XI d` (itself from `jetPreOkF`, PreJBridge).  Not zero-knowledge.
-/
import NockvmE2E.Z38.IfaceJ
import NockvmE2E.J9AL.LagrJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.Z38.LagrJ9ALJ

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.MaskOk NockvmE2E.Exec.MaskBridge NockvmE2E.Exec.MaskBridge9 NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.MaskOkK (polyOfArr)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.LagrJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.LagrJ9AL
open NockvmE2E.J8.InstJ8 (P Φ0 ω0 preOf)
open NockvmE2E.J8 (RapAirJ TabRestr)
open NockvmE2E.Z38.IfaceJ

theorem preJ9_s3 (d : Datum9A) (c : ℕ) (hc : c < 18) :
    preJ9 d (colI9 3 c) = some (Lagrange.interpolate Finset.univ d.Pb.nodesJ (fun i => Nock.Jet.ChipJ8.jetPre d.Pb.lay c i)) := by
  show preOf _ _ = _
  rw [preOf_of_idx _ _ ⟨c, hc⟩ (by show c = c % 71; exact (Nat.mod_eq_of_lt (by omega)).symm)]
  rfl

theorem preIdx_jet : famJ9AL.preIdx "jetChipJ8" = Array.range 18 := by
  rw [(famJ9AL_j9a _ (by decide)).2.1]
  simp [famJ9A, preIdx9, J8Shape.preIdxJ8]

section Bridge
variable {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
  (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
  (npub : ℕ) (tp : Fin (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Jm.T) (hcap : (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Cap npub)

theorem hjet_of_PreJLink (hpreJ : PreJLink XI d) :
    ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "jetChipJ8" → ∀ c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 1 → LagrAt9 (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t c := by
  intro t hid c hc hk
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have hpk : ((XI.colKind[XI.tabs[t].col0 + c]! == 1) == (famJ9AL.preIdx XI.tabs[t].chip.id).contains c) = true := by
    have hpk0 := preKindOk_of_shapeF hsh
    unfold preKindOkF at hpk0
    have := (Array.all_eq_true_iff_forall_mem.mp hpk0) XI.tabs[t] (Array.mem_def.mpr hm)
    simp only [List.all_eq_true, List.mem_range] at this
    exact this c hc
  rw [hk, hid, preIdx_jet] at hpk
  have hc18 : c < 18 := by
    have : (Array.range 18).contains c = true := by simpa using hpk
    simpa using Array.contains_iff_mem.mp this
  have hsd : sigma9L XI t = tabIdx9L XI.tabs[t].chip.id := rfl
  have hs : sigma9L XI t = 3 := by rw [hsd, hid]; rfl
  have h1 : (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = preJ9L d (colI9L (sigma9L XI t) c) := rfl
  unfold LagrAt9
  show (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = _
  rw [h1, hs]
  show preJ9 d.toA (colI9 3 c) = _
  rw [preJ9_s3 d.toA c hc18]
  show _ = some _
  rw [← polyOfArr_sum]
  exact congrArg some (hpreJ t hid c hc18)

end Bridge

end NockvmE2E.Z38.LagrJ9ALJ

#print axioms NockvmE2E.Z38.LagrJ9ALJ.preJ9_s3
#print axioms NockvmE2E.Z38.LagrJ9ALJ.preIdx_jet
#print axioms NockvmE2E.Z38.LagrJ9ALJ.hjet_of_PreJLink
