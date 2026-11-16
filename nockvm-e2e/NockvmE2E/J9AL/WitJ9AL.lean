/-
`Wit9L XI c Q`, the datum-side witness of the J-9 AL headline, and `witness9L` (twin of `Wit9` / `witness9` of
`J9A/E2EJ9AToyR.lean` §3).  `witness9L` takes the link gate's proposition `LinkOK9L XI c`, the family shape, `pregOkF` and the canonicity of the public
input; no toys.  Not zero-knowledge.
-/
import NockvmE2E.J9AL.DatX9LOk
import NockvmE2E.J9AL.InstJ9ALW
import NockvmE2E.J9AL.RVUJ9AL
import NockvmE2E.J9A.E2EJ9AToyR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.WitJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L NockvmE2E.J9AL.PregJ9AL NockvmE2E.J9AL.DatX9LOk
  NockvmE2E.J9AL.InstJ9ALW NockvmE2E.J9AL.LagrJ9AL NockvmE2E.J9AL.RVUJ9AL
open NockvmE2E.J9A.RunGate9L (LinkOK9L PrimsLink kOfL kVOfL pregOkF)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (primCode)

/-- **`Wit9L XI c Q`**: there is a J-9 AL datum `d` with `DatumOK9AL d`, `Link9L XI d`, `StmtP9AL d`, `InpLink9L d XI.pubIn`, `PrimsCan XI.pubIn`, small registry ids,
the numeral side condition `hnum0` (the ALU's numeral is `0`), the five absent-table layout conditions, `PreLLink XI d`, no jet table, the table restriction
`R` with `hfree`, `d.c = c`, and `Q d`.  These are the datum-side binders of `exec_e2e_J9AL` (with `XI := XI170 XI0`). -/
def Wit9L (XI : ExecInst) (c : P8PublicClaim) (Q : Datum9AL → Prop) : Prop :=
  ∃ (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d),
    StmtP9AL d ∧ InpLink9L d XI.pubIn ∧ PrimsCan XI.pubIn ∧ (∀ id ∈ d.Pb.regs, id < P) ∧
    (∀ t : Fin XI.tabs.size, (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = numOf9L d (sigma9L XI t)) ∧
    (d.Pb.nJ = 0 → XI.pubLay.present[3]! = false) ∧ (d.Pb.krootsV = 0 → XI.pubLay.present[5]! = false) ∧
    (d.Pb.axOn = false → XI.pubLay.present[6]! = false) ∧ (d.Pb.spOn = false → XI.pubLay.present[7]! = false) ∧
    (d.Pb.aluOn = false → XI.pubLay.present[8]! = false) ∧
    PreLLink XI d ∧
    (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "jetChipJ8") ∧
    (∃ (R : NockvmE2E.J8.TabRestr (NockvmE2E.J9AL.GenJ9AL.J9AL d hdk)) (hT : R.T' = XI.tabs.size),
      (∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) ∧ (NockvmE2E.J9AL.GenJ9AL.J9AL d hdk).AccOn R.q) ∧
    d.c = c ∧ Q d

/-- `inpCanOkL` as a proposition on the public input (`based = < PN`), twin of `PrimsCan`'s five fields -/
theorem sigma9L_castSucc (XI : ExecInst) (t : Fin XI.tabs.size) (h : XI.tabs[t].chip.id ≠ "aluChipJ9") :
    sigma9L XI t = (sigma9 XI t).castSucc := by
  unfold sigma9L tabIdx9L sigma9
  rw [if_neg h]

theorem sigma9L_alu (XI : ExecInst) (t : Fin XI.tabs.size) (h : XI.tabs[t].chip.id = "aluChipJ9") :
    sigma9L XI t = 8 := by
  unfold sigma9L tabIdx9L
  rw [if_pos h]

theorem numOf9L_castSucc (d : Datum9AL) (s : Fin 8) : numOf9L d s.castSucc = NockvmE2E.J9A.LagrJ9A.numOf9 d.toA s := by
  unfold numOf9L
  have : (s.castSucc : Fin 9).val < 8 := s.2
  simp [this]

theorem numOf9L_last (d : Datum9AL) : numOf9L d 8 = 0 := by
  unfold numOf9L; simp

/-- the unique-id lookup: with `Nodup` ids, the first record with `r.id` is `r` -/
theorem find_id (ps : List PE.PrimRec) (hnd : (ps.map PE.PrimRec.id).Nodup) :
    ∀ r ∈ ps, ps.find? (fun q => q.id == r.id) = some r := by
  induction ps with
  | nil => intro r hr; simp at hr
  | cons a l ih =>
    intro r hr
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hr with rfl | hr'
    · simp [List.find?_cons]
    · have hne : a.id ≠ r.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hr')
      simp [List.find?_cons, hne, ih hnd.2 r hr']

/-- the datum's `prims` re-encode (with `idxP`, `rkP` the lookups) to the public input's `prims` -/
theorem hprim_PbOfX9L (XI : ExecInst) (hrt : NockvmE2E.J9A.RunGate9L.primsRoundTrip XI.pubIn.prims = true)
    (hnd : (XI.pubIn.prims.map PE.PrimRec.id).Nodup) :
    XI.pubIn.prims = (primsOf XI).map fun q =>
      (⟨q.1, primCode q.2, idxPOf XI q.1, (rkPOf XI q.1).1, (rkPOf XI q.1).2⟩ : PE.PrimRec) := by
  obtain ⟨qs, hqs, hmap⟩ := roundtrip_data _ hrt
  rw [primsOf_eq XI qs hqs]
  have h1 : qs.map (fun q => (⟨q.1, primCode q.2, idxPOf XI q.1, (rkPOf XI q.1).1, (rkPOf XI q.1).2⟩ : PE.PrimRec)) =
      (qs.map (fun q => (q.1, primCode q.2))).map
        (fun a => (⟨a.1, a.2, idxPOf XI a.1, (rkPOf XI a.1).1, (rkPOf XI a.1).2⟩ : PE.PrimRec)) := by
    simp [List.map_map, Function.comp_def]
  rw [h1, hmap]
  conv_lhs => rw [← List.map_id XI.pubIn.prims]
  simp only [List.map_map]
  refine List.map_congr_left (fun r hr => ?_)
  have hf := find_id _ hnd r hr
  simp only [Function.comp, id, idxPOf, rkPOf, hf, Option.map_some, Option.getD_some]

theorem witness9L (XI : ExecInst) (c : P8PublicClaim) (h : shapeOkF famJ9AL XI = true)
    (hpreg : pregOkF XI = true) (hcan : PrimsCan XI.pubIn) (hL : LinkOK9L XI c)
    (Q : Datum9AL → Prop) (hQ : ∀ hJ : hNof XI "jetChipJ8" = 0, Q (DX9L XI h hJ (kOfL XI) (kVOfL XI) c)) :
    Wit9L XI c Q := by
  have hL' := hL
  obtain ⟨hJ, hk1, hkW, hV, hV0, ⟨hc1, hc2, hc3⟩, hcl, hpin, hat, hnum, hnumL, hpJ, hpV, hpX, hpS, hnj, hpl⟩ := hL'
  obtain ⟨hdk, hS⟩ := datX9L_ok XI h hJ (kOfL XI) (kVOfL XI) hk1 hkW hV hV0 c ⟨hc1, hc2, hc3⟩ hpreg hpl
  obtain ⟨hrt, hprb, hnd, -, -, -, habs⟩ := hpl
  refine ⟨DX9L XI h hJ (kOfL XI) (kVOfL XI) c, hdk, link9L_DX9L XI h hJ _ _ c, hS, ⟨⟨hcl, hpin, hat⟩, ?_⟩, hcan, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnj,
    ⟨RJ9AL XI _ hdk, rfl, fun _ => rfl, hfree_J9AL XI h _ _ _ [] [] _ _ _ _ rfl hdk⟩, rfl, hQ hJ⟩
  · exact hprim_PbOfX9L XI hrt hnd
  · intro id hid; exact absurd hid (by simp [DX9L, PbOfX9L])
  · intro t
    by_cases ha : XI.tabs[t].chip.id = "aluChipJ9"
    · rw [sigma9L_alu XI t ha, numOf9L_last]; exact hnumL t ha
    · rw [sigma9L_castSucc XI t ha, numOf9L_castSucc]; exact hnum t ha
  · exact hpJ
  · exact hpV
  · exact hpX
  · exact hpS
  · intro hoff
    exact (habs hoff).2
  · intro t hid k
    exact preL_PbOfX9L XI h t hid k

end NockvmE2E.J9AL.WitJ9AL

#print axioms NockvmE2E.J9AL.WitJ9AL.hprim_PbOfX9L
#print axioms NockvmE2E.J9AL.WitJ9AL.witness9L
